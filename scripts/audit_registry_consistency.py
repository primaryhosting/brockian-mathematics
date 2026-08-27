#!/usr/bin/env python3
"""Read-only consistency audit for the Brockian theorem registry.

Inputs:
  - registry/theorems.json
  - provenance/verdicts.yaml
  - Brockian.lean and registry/attestations/*.json for noncanonical-attestation smells
  - source files referenced by CONJECTURE entries, only to confirm Prop-container shape

The script deliberately does not regenerate or rewrite registry outputs.
It is stdlib-only; if PyYAML is installed, the YAML provenance is also checked.
"""
from __future__ import annotations

import argparse
import json
import re
import textwrap
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


VALID_RUNGS = {"classical", "literature", "open"}
OPEN_REGISTERS = {"CONDITIONAL", "CONJECTURE"}
# ALLOWED_AXIOMS is single-sourced from engine.verify — the derivation rule, this audit,
# and the firewall all import the one definition, so the allowed axiom set cannot drift.
import sys as _sys
_sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from engine.verify import ALLOWED_AXIOMS  # noqa: E402
SUMMARY_ORDER = [
    "PROVED",
    "CONDITIONAL",
    "CONJECTURE",
    "DEFINITION",
    "COMPUTATION",
    "UNVERIFIED",
]

OPEN_STRENGTH_PATTERNS = [
    (re.compile(r"\bOPEN\b", re.IGNORECASE), "OPEN"),
    (re.compile(r"\bopen-strength\b", re.IGNORECASE), "open-strength"),
    (re.compile(r"\bCONDITIONAL\b", re.IGNORECASE), "CONDITIONAL"),
    (re.compile(r"\bconditional on\b", re.IGNORECASE), "conditional on"),
    (re.compile(r"\bconjectur(?:e|al)\b", re.IGNORECASE), "conjecture/conjectural"),
    (re.compile(r"\bMathlib-absent\b", re.IGNORECASE), "Mathlib-absent"),
    (re.compile(r"\bnot citable\b", re.IGNORECASE), "not citable"),
    (re.compile(r"\bnot shown instantiable\b", re.IGNORECASE), "not shown instantiable"),
    (re.compile(r"\bGIVEN\b", re.IGNORECASE), "GIVEN"),
]


@dataclass(frozen=True)
class Finding:
    level: str
    code: str
    subject: str
    detail: str


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as f:
        data = json.load(f)
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected a JSON object")
    return data


def load_yaml_optional(path: Path) -> tuple[dict[str, Any], str | None]:
    try:
        import yaml  # type: ignore[import-not-found]
    except ModuleNotFoundError:
        return {}, "PyYAML unavailable; using registry-embedded provenance only."

    if not path.exists():
        return {}, f"{path}: missing; using registry-embedded provenance only."
    with path.open(encoding="utf-8") as f:
        data = yaml.safe_load(f) or {}
    if not isinstance(data, dict):
        return {}, f"{path}: expected a YAML mapping; using registry-embedded provenance only."
    return data, None


def strip_lean_comments(text: str) -> str:
    """Blank Lean comments, including nested block comments, preserving newlines."""
    out = list(text)
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith("--", i) and depth == 0:
            j = text.find("\n", i)
            if j == -1:
                j = len(text)
            for k in range(i, j):
                out[k] = " "
            i = j
            continue
        if text.startswith("/-", i):
            depth += 1
            out[i] = " "
            out[i + 1] = " "
            i += 2
            continue
        if text.startswith("-/", i) and depth > 0:
            depth -= 1
            out[i] = " "
            out[i + 1] = " "
            i += 2
            continue
        if depth > 0 and text[i] != "\n":
            out[i] = " "
        i += 1
    return "".join(out)


def short_name(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def normalized_identifier(name: str) -> str:
    snake = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", short_name(name))
    return "".join(tok.lower() for tok in re.split(r"[^A-Za-z0-9]+", snake) if tok)


def normalized_statement(statement: Any) -> str:
    if not statement:
        return ""
    return re.sub(r"\s+", " ", str(statement)).strip().lower()


def entry_note_text(entry: dict[str, Any]) -> str:
    fields = [
        entry.get("ledger_run"),
        entry.get("provenance_note"),
        entry.get("conditional_rung"),
    ]
    return " ".join(str(x) for x in fields if x)


def yaml_module_contexts(verdicts: dict[str, Any]) -> dict[str, dict[str, Any]]:
    contexts: dict[str, dict[str, Any]] = {}
    for run_id, run in (verdicts.get("runs") or {}).items():
        if not isinstance(run, dict):
            continue
        module = run.get("module")
        if not isinstance(module, str) or not module:
            continue
        contexts[module] = {"run_id": str(run_id), **run}
    return contexts


def yaml_decl_contexts(verdicts: dict[str, Any]) -> dict[str, dict[str, Any]]:
    contexts: dict[str, dict[str, Any]] = {}
    for run_id, run in (verdicts.get("runs") or {}).items():
        if not isinstance(run, dict):
            continue
        module = run.get("module")
        if not isinstance(module, str) or not module:
            continue
        base = {"run_id": str(run_id), **run}
        for override in run.get("overrides") or []:
            if not isinstance(override, dict) or not override.get("name"):
                continue
            ctx = dict(base)
            ctx.update(override)
            contexts[f"{module}.{override['name']}"] = ctx
    return contexts


def root_import_stems(root: Path) -> set[str]:
    if not root.exists():
        return set()
    stems = set()
    for line in root.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if stripped.startswith("import Brockian."):
            stems.add(stripped.removeprefix("import Brockian."))
    return stems


def conjecture_is_prop_container(repo: Path, entry: dict[str, Any]) -> tuple[bool, str]:
    source = (entry.get("source") or {}).get("file")
    if not source:
        return False, "missing source file metadata"
    path = repo / str(source)
    if not path.exists():
        return False, f"source file does not exist: {source}"
    text = strip_lean_comments(path.read_text(encoding="utf-8"))
    name = short_name(str(entry.get("name", "")))
    pattern = re.compile(
        rf"^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?(?:def|abbrev)\s+"
        rf"{re.escape(name)}\b(?P<sig>.*?):=\s*",
        re.MULTILINE | re.DOTALL,
    )
    match = pattern.search(text)
    if not match:
        return False, f"could not find a def/abbrev declaration for {name}"
    sig = re.sub(r"\s+", " ", match.group("sig")).strip()
    if not re.search(r":\s*Prop\b", sig):
        return False, f"declaration signature is not visibly Prop-typed: {sig[:120]}"
    before_colon = sig.split(":", 1)[0].strip()
    if before_colon:
        return False, f"Prop declaration appears parameterized before ':': {before_colon}"
    return True, "nullary Prop def/abbrev container"


def find_duplicates(entries: list[dict[str, Any]]) -> list[Finding]:
    findings: list[Finding] = []
    by_name: dict[str, list[dict[str, Any]]] = defaultdict(list)
    by_short_module: dict[tuple[str, str], list[dict[str, Any]]] = defaultdict(list)
    for entry in entries:
        name = str(entry.get("name", ""))
        by_name[name].append(entry)
        by_short_module[(str(entry.get("module", "")), short_name(name))].append(entry)
    for name, group in sorted(by_name.items()):
        if len(group) > 1:
            registers = ", ".join(str(e.get("register")) for e in group)
            findings.append(
                Finding("ERROR", "duplicate-name", name, f"{len(group)} entries: {registers}")
            )
    for (module, short), group in sorted(by_short_module.items()):
        full_names = {str(e.get("name", "")) for e in group}
        if len(group) > 1 and len(full_names) > 1:
            findings.append(
                Finding(
                    "WARN",
                    "duplicate-short-name",
                    f"{module}.{short}",
                    ", ".join(sorted(full_names)),
                )
            )
    return findings


def find_open_consistency(
    repo: Path,
    entries: list[dict[str, Any]],
    verdicts: dict[str, Any],
) -> list[Finding]:
    findings: list[Finding] = []
    module_ctx = yaml_module_contexts(verdicts)
    decl_ctx = yaml_decl_contexts(verdicts)
    for entry in entries:
        register = str(entry.get("register", ""))
        name = str(entry.get("name", ""))
        if register == "CONDITIONAL":
            rung = entry.get("conditional_rung")
            if rung not in VALID_RUNGS:
                findings.append(
                    Finding(
                        "ERROR",
                        "conditional-rung",
                        name,
                        f"conditional_rung must be one of {sorted(VALID_RUNGS)}, got {rung!r}",
                    )
                )
            if not entry.get("ledger_run") or not entry.get("provenance_note"):
                findings.append(
                    Finding(
                        "WARN",
                        "conditional-provenance",
                        name,
                        "missing ledger_run or provenance_note in registry entry",
                    )
                )
            if verdicts:
                ctx = decl_ctx.get(name) or module_ctx.get(str(entry.get("module", "")))
                if not ctx:
                    findings.append(
                        Finding("WARN", "conditional-yaml", name, "missing provenance run/override")
                    )
                elif ctx.get("conditional_rung") != rung:
                    findings.append(
                        Finding(
                            "WARN",
                            "conditional-yaml-rung",
                            name,
                            f"registry has {rung!r}; YAML context has {ctx.get('conditional_rung')!r}",
                        )
                    )
        elif register == "CONJECTURE":
            kind = str(entry.get("kind", ""))
            if kind != "conjecture":
                findings.append(
                    Finding("ERROR", "conjecture-kind", name, f"kind is {kind!r}, expected 'conjecture'")
                )
            ok, detail = conjecture_is_prop_container(repo, entry)
            if not ok:
                findings.append(Finding("ERROR", "conjecture-shape", name, detail))
            if not entry.get("ledger_run") or not entry.get("provenance_note"):
                findings.append(
                    Finding(
                        "WARN",
                        "conjecture-provenance",
                        name,
                        "missing ledger_run or provenance_note in registry entry",
                    )
                )
    return findings


def find_register_invariants(entries: list[dict[str, Any]]) -> list[Finding]:
    """Re-derive the register invariant on the committed registry entries themselves.

    gen_registry derives registers, but registry/theorems.json is the committed
    source of truth — a hand-edited or drifted entry could claim PROVED while its
    own recorded facts contradict it. This section catches exactly that.
    """
    findings: list[Finding] = []
    for entry in entries:
        register = str(entry.get("register", ""))
        name = str(entry.get("name", ""))

        raw_flags = entry.get("flags")
        flags = raw_flags if isinstance(raw_flags, dict) else {}
        raw_ver = entry.get("verification")
        ver = raw_ver if isinstance(raw_ver, dict) else {}
        raw_axle = ver.get("axle")
        axle = raw_axle if isinstance(raw_axle, dict) else {}
        raw_axioms = entry.get("axioms")
        axioms = raw_axioms if isinstance(raw_axioms, list) else None

        if register == "PROVED":
            malformed = []
            if axioms is None:
                malformed.append("axioms")
            if raw_flags is not None and not isinstance(raw_flags, dict):
                malformed.append("flags")
            if raw_ver is not None and not isinstance(raw_ver, dict):
                malformed.append("verification")
            if isinstance(raw_ver, dict) and raw_axle is not None and not isinstance(raw_axle, dict):
                malformed.append("verification.axle")
            if malformed:
                findings.append(
                    Finding("ERROR", "proved-malformed", name,
                            f"missing or wrong-typed field(s): {', '.join(malformed)}")
                )
            extra = set(axioms or []) - ALLOWED_AXIOMS
            if extra:
                findings.append(
                    Finding("ERROR", "proved-invariant", name,
                            f"axioms escape allowed set: {sorted(extra)}")
                )
            for key in ("sorry", "native_decide", "exact_search"):
                if flags.get(key):
                    findings.append(
                        Finding("ERROR", "proved-invariant", name, f"flags.{key} is true")
                    )
            if axle.get("verdict") != "verified":
                findings.append(
                    Finding("ERROR", "proved-invariant", name,
                            f"axle verdict is {axle.get('verdict')!r}, not 'verified'")
                )
            if ver.get("axioms_ok") is not True:
                findings.append(
                    Finding("ERROR", "proved-invariant", name,
                            f"verification.axioms_ok is {ver.get('axioms_ok')!r}, not true")
                )
            if entry.get("verification_quarantine") or ver.get("quarantine"):
                findings.append(
                    Finding("ERROR", "proved-invariant", name,
                            "verification quarantine is active on a PROVED entry")
                )
            if entry.get("conditional_rung") is not None:
                findings.append(
                    Finding("ERROR", "proved-invariant", name,
                            f"conditional_rung is {entry.get('conditional_rung')!r} on a PROVED entry")
                )
        elif register in ("CONDITIONAL", "DISCHARGED"):
            # flags.sorry mirrors sorryAx in gen_registry output; check both so
            # single-field drift is still caught.
            if "sorryAx" in (axioms or []) or flags.get("sorry"):
                findings.append(
                    Finding("ERROR", "open-register-sorry", name,
                            "entry records sorryAx/flags.sorry — a sorry-backed proof "
                            "cannot carry an open register")
                )
    return findings


def find_missing_provenance(entries: list[dict[str, Any]]) -> list[Finding]:
    findings: list[Finding] = []
    for entry in entries:
        register = str(entry.get("register", ""))
        if register == "DEFINITION":
            continue
        if not entry.get("ledger_run") or not entry.get("provenance_note"):
            findings.append(
                Finding(
                    "INFO",
                    "missing-provenance",
                    str(entry.get("name", "")),
                    f"{register} entry lacks ledger_run or provenance_note",
                )
            )
    return findings


def same_target(open_entry: dict[str, Any], proved_entry: dict[str, Any]) -> str | None:
    open_statement = normalized_statement(open_entry.get("statement"))
    proved_statement = normalized_statement(proved_entry.get("statement"))
    if open_statement and proved_statement and open_statement == proved_statement:
        return "same normalized statement"

    open_norm = normalized_identifier(str(open_entry.get("name", "")))
    proved_norm = normalized_identifier(str(proved_entry.get("name", "")))
    proof_words = ("proof", "proved", "verified", "theorem", "holds", "true")
    for suffix in proof_words:
        if proved_norm == open_norm + suffix:
            return f"proved name is open target plus '{suffix}'"
    return None


def find_stale_open_entries(entries: list[dict[str, Any]]) -> list[Finding]:
    findings: list[Finding] = []
    proved = [e for e in entries if e.get("register") == "PROVED"]
    opens = [e for e in entries if e.get("register") in OPEN_REGISTERS]
    proved_by_module: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for entry in proved:
        proved_by_module[str(entry.get("module", ""))].append(entry)
    for entry in opens:
        for candidate in proved_by_module.get(str(entry.get("module", "")), []):
            reason = same_target(entry, candidate)
            if reason:
                findings.append(
                    Finding(
                        "WARN",
                        "stale-open",
                        str(entry.get("name", "")),
                        f"matches PROVED {candidate.get('name')} ({reason})",
                    )
                )
    return findings


def find_attestation_smells(repo: Path, attest_dir: Path, root: Path) -> list[Finding]:
    findings: list[Finding] = []
    imported = root_import_stems(root)
    att_files = sorted(attest_dir.glob("*.json"))
    att_stems = {p.stem for p in att_files}
    for stem in sorted(att_stems - imported):
        findings.append(
            Finding(
                "WARN",
                "attestation-not-root-imported",
                stem,
                "attestation file is ignored by root-import-filtered registry unless Brockian.lean imports it",
            )
        )
    for stem in sorted(imported - att_stems):
        findings.append(
            Finding(
                "INFO",
                "root-import-without-attestation",
                stem,
                "root import has no same-stem attestation; this can be normal for non-registered modules",
            )
        )
    modules: dict[str, list[str]] = defaultdict(list)
    for path in att_files:
        try:
            att = load_json(path)
        except Exception as exc:  # noqa: BLE001 - report malformed registry input
            findings.append(Finding("ERROR", "attestation-json", path.name, str(exc)))
            continue
        module = str(att.get("module", ""))
        modules[module].append(path.name)
        if not module.startswith("Brockian."):
            findings.append(
                Finding("WARN", "attestation-module", path.name, f"module is {module!r}")
            )
        if not isinstance(att.get("declarations"), list):
            findings.append(
                Finding("ERROR", "attestation-declarations", path.name, "missing declarations list")
            )
        if att.get("module_verified") is not True:
            findings.append(
                Finding(
                    "ERROR",
                    "attestation-unverified",
                    path.name,
                    f"module_verified is {att.get('module_verified')!r}",
                )
            )
        for dec in att.get("declarations") or []:
            if not isinstance(dec, dict):
                continue
            name = str(dec.get("name", ""))
            quarantined = dec.get("verification_quarantine") is True
            if "sorryAx" in (dec.get("axioms") or []):
                findings.append(
                    Finding("ERROR", "attestation-sorry-axiom", path.name,
                            f"{name} axioms include sorryAx (proof-by-sorry)")
                )
            if (dec.get("kind", "theorem") in ("theorem", "lemma")
                    and not quarantined and dec.get("axioms_ok") is not True):
                findings.append(
                    Finding("ERROR", "attestation-axioms-not-ok", path.name,
                            f"{name} axioms_ok is not true")
                )
            if not quarantined and dec.get("axle_verdict") == "failed":
                findings.append(
                    Finding("ERROR", "attestation-axle-failed", path.name,
                            f"{name} axle_verdict is 'failed'")
                )
    for module, names in sorted(modules.items()):
        if module and len(names) > 1:
            findings.append(
                Finding("WARN", "duplicate-attestation-module", module, ", ".join(sorted(names)))
            )
    return findings


def find_proved_note_smells(entries: list[dict[str, Any]]) -> list[Finding]:
    findings: list[Finding] = []
    for entry in entries:
        if entry.get("register") != "PROVED":
            continue
        text = entry_note_text(entry)
        hits = []
        for pattern, label in OPEN_STRENGTH_PATTERNS:
            if pattern.search(text):
                hits.append(label)
        if hits:
            findings.append(
                Finding(
                    "INFO",
                    "proved-open-strength-note",
                    str(entry.get("name", "")),
                    f"note contains open-strength phrase(s): {', '.join(sorted(set(hits)))}",
                )
            )
    return findings


def recount(entries: Iterable[dict[str, Any]]) -> Counter[str]:
    return Counter(str(e.get("register", "UNKNOWN")) for e in entries)


def ordered_summary(counter: Counter[str]) -> list[tuple[str, int]]:
    seen = set()
    pairs = []
    for key in SUMMARY_ORDER:
        if key in counter:
            pairs.append((key, counter[key]))
            seen.add(key)
    for key in sorted(counter):
        if key not in seen:
            pairs.append((key, counter[key]))
    return pairs


def print_findings(title: str, findings: list[Finding], limit: int | None) -> None:
    print(title)
    if not findings:
        print("  none")
        print()
        return
    shown = findings if limit is None else findings[:limit]
    for finding in shown:
        print(f"- [{finding.level}] {finding.code}: {finding.subject}")
        wrapped = textwrap.wrap(
            finding.detail,
            width=100,
            initial_indent="  ",
            subsequent_indent="  ",
            break_long_words=False,
            break_on_hyphens=False,
        )
        for line in wrapped:
            print(line)
    if limit is not None and len(findings) > limit:
        print(f"  ... {len(findings) - limit} more")
    print()


def main() -> int:
    repo = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--registry", type=Path, default=repo / "registry" / "theorems.json")
    parser.add_argument("--provenance", type=Path, default=repo / "provenance" / "verdicts.yaml")
    parser.add_argument("--root-imports", type=Path, default=repo / "Brockian.lean")
    parser.add_argument("--attestations", type=Path, default=repo / "registry" / "attestations")
    parser.add_argument("--strict", action="store_true", help="exit nonzero on ERROR findings")
    parser.add_argument(
        "--limit",
        type=int,
        default=40,
        help="maximum findings per section; use 0 for no limit",
    )
    args = parser.parse_args()

    registry = load_json(args.registry)
    entries = registry.get("theorems")
    if not isinstance(entries, list):
        raise ValueError(f"{args.registry}: expected 'theorems' to be a list")

    verdicts, yaml_warning = load_yaml_optional(args.provenance)
    limit = None if args.limit == 0 else args.limit

    summary = recount(entries)
    declared_summary = Counter(
        {str(k): int(v) for k, v in (registry.get("summary") or {}).items()}
    )

    all_findings: list[Finding] = []
    if declared_summary and declared_summary != summary:
        all_findings.append(
            Finding(
                "ERROR",
                "summary-mismatch",
                str(args.registry),
                f"embedded summary {dict(declared_summary)} != recount {dict(summary)}",
            )
        )

    sections = [
        ("Open-entry consistency", find_open_consistency(repo, entries, verdicts)),
        ("Register invariants", find_register_invariants(entries)),
        ("Missing provenance", find_missing_provenance(entries)),
        ("Stale open entries", find_stale_open_entries(entries)),
        ("Duplicate names", find_duplicates(entries)),
        ("Attestation smells", find_attestation_smells(repo, args.attestations, args.root_imports)),
        ("Open-strength phrases in PROVED notes", find_proved_note_smells(entries)),
    ]
    for _, findings in sections:
        all_findings.extend(findings)

    print("Registry consistency audit")
    print(f"  registry: {args.registry}")
    print(f"  provenance: {args.provenance}")
    print(f"  root imports: {args.root_imports}")
    print(f"  attestations: {args.attestations}")
    if yaml_warning:
        print(f"  warning: {yaml_warning}")
    print()
    print("Summary")
    print(f"  total entries: {len(entries)}")
    for key, value in ordered_summary(summary):
        print(f"  {key}: {value}")
    print()

    for title, findings in sections:
        print_findings(title, findings, limit)

    levels = Counter(f.level for f in all_findings)
    print("Finding counts")
    for level in ("ERROR", "WARN", "INFO"):
        print(f"  {level}: {levels[level]}")

    return 1 if args.strict and levels["ERROR"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
