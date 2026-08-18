"""Generate registry/theorems.json from the compiled environment + AXLE verdicts +
provenance/verdicts.yaml.

The register is DERIVED (never hand-asserted) from three inputs (spec 5):
  - build-derived: axioms, flags (native_decide / sorry / exact_search)
  - external attestation: the AXLE independent verdict
  - provenance-map: conditional_rung (and ledger_run / quarantine / provenance_note)

`derive_register` is the load-bearing rule and is unit-tested in isolation. The rest of
this module wires extraction + merge + artifact emission and is exercised end-to-end once
the Lean core builds.
"""
from __future__ import annotations

import glob
import json
import os
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from typing import Any, Optional

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
VALID_RUNGS = {"classical", "literature", "open"}


@dataclass
class Flags:
    native_decide: bool = False
    sorry: bool = False
    exact_search: bool = False


@dataclass
class DeclFacts:
    name: str
    kind: str  # "theorem" | "lemma" | "def"
    axioms: list[str] = field(default_factory=list)
    flags: Flags = field(default_factory=Flags)
    axle_verified: Optional[bool] = None  # None = not yet checked
    conditional_rung: Optional[str] = None  # classical | literature | open


def derive_register(f: DeclFacts) -> str:
    """Compute the register from build facts + AXLE verdict + rung (spec 4).

    Precedence:
      CONJECTURE  — a def / Prop container (not a theorem/lemma)
      CONDITIONAL — depends on a named hypothesis (conditional_rung set)
      COMPUTATION — relies on decide / native_decide finite checks
      PROVED      — sorry-free, axioms ⊆ allowed, no native_decide/exact?,
                    AND an independent AXLE verdict == verified
    A declaration that would be PROVED but fails any leg falls back to COMPUTATION
    (if native_decide) else is reported UNVERIFIED so it can never masquerade as proved.
    """
    if f.kind == "conjecture":
        return "CONJECTURE"
    if f.kind in ("def", "abbrev"):
        return "DEFINITION"
    if f.kind not in ("theorem", "lemma"):
        return "CONJECTURE"
    if f.conditional_rung is not None:
        if f.conditional_rung not in VALID_RUNGS:
            raise ValueError(f"{f.name}: invalid conditional_rung {f.conditional_rung!r}")
        return "CONDITIONAL"
    if f.flags.native_decide:
        return "COMPUTATION"
    axioms_ok = set(f.axioms).issubset(ALLOWED_AXIOMS)
    clean = axioms_ok and not f.flags.sorry and not f.flags.exact_search
    if clean and f.axle_verified is True:
        return "PROVED"
    return "UNVERIFIED"


def build_entry(f: DeclFacts, prov: dict[str, Any], source: dict[str, Any],
                statement: str, axle_env: Optional[str]) -> dict[str, Any]:
    register = derive_register(f)
    return {
        "name": f.name,
        "kind": f.kind,
        "module": prov.get("module", ""),
        "statement": statement,
        "source": source,
        "register": register,
        "axioms": sorted(f.axioms),
        "flags": {
            "native_decide": f.flags.native_decide,
            "sorry": f.flags.sorry,
            "exact_search": f.flags.exact_search,
        },
        "verification": {
            "lake_build": prov.get("lake_build", "pending"),
            "axioms_ok": set(f.axioms).issubset(ALLOWED_AXIOMS),
            "axle": {
                "verdict": ("verified" if f.axle_verified is True
                            else "failed" if f.axle_verified is False else "pending"),
                "environment": axle_env,
            },
        },
        "conditional_rung": f.conditional_rung,
        "discharged_by": prov.get("discharged_by"),
        "quarantine": bool(prov.get("quarantine", False)),
        "ledger_run": prov.get("ledger_run"),
        "provenance_note": prov.get("provenance_note"),
    }


# ── end-to-end generation from AXLE attestations + provenance/verdicts.yaml ──────

def _load_verdicts(path: str) -> dict[str, Any]:
    import yaml  # pyyaml
    if not __import__("os").path.exists(path):
        return {"closed_modules": [], "runs": {}}
    return yaml.safe_load(open(path)) or {"closed_modules": [], "runs": {}}


def _provenance_for(module: str, name: str, verdicts: dict[str, Any]) -> dict[str, Any]:
    """Resolve provenance for a fully-qualified decl by module (run-level default) then
    per-declaration override (spec §3.2)."""
    short = name.split(".")[-1]
    for run in (verdicts.get("runs") or {}).values():
        if run.get("module") != module:
            continue
        prov = {k: run.get(k) for k in ("module", "quarantine", "ledger_run",
                                        "provenance_note", "conditional_rung",
                                        "kind_override", "discharged_by")}
        for ov in (run.get("overrides") or []):
            if ov.get("name") == short:
                prov.update({k: v for k, v in ov.items() if k != "name"})
        return prov
    return {"module": module}


def generate(attest_dir: str, verdicts_path: str) -> dict[str, Any]:
    """Build the registry from registry/attestations/*.json + verdicts.yaml.

    Uses AXLE attestations as the verification source of truth (independent, at a named
    environment). The local `lake_build` field is left "pending" until a local build
    stamps it — AXLE alone still yields a fully-derived register.
    """
    import glob
    import os
    verdicts = _load_verdicts(verdicts_path)
    # Tie the registry to the ACTUAL build: only attestations for modules imported in
    # Brockian.lean count. This makes the registry robust against stray attestation files
    # left by parallel tools (Grok/Codex) for non-integrated / non-verifying modules.
    built = None
    root = "Brockian.lean"
    if os.path.exists(root):
        built = set()
        for line in open(root):
            line = line.strip()
            if line.startswith("import Brockian."):
                built.add(line.split(".", 1)[1])  # e.g. "WeylChain"  (attestation file stem)
    entries: list[dict[str, Any]] = []
    for ap in sorted(glob.glob(os.path.join(attest_dir, "*.json"))):
        stem = os.path.basename(ap)[:-5]
        if built is not None and stem not in built:
            continue  # skip attestations not backed by a root import (stray/parallel-tool)
        # Fail LOUD (naming the offending file) on malformed attestations — never
        # skip, since skipping silently shrinks the registry (the dishonest direction).
        try:
            att = json.load(open(ap))
        except json.JSONDecodeError as exc:
            raise ValueError(f"{ap}: malformed attestation JSON: {exc}") from exc
        if not isinstance(att.get("module"), str) or not isinstance(att.get("declarations"), list):
            raise ValueError(f"{ap}: malformed attestation (module/declarations)")
        module = att["module"]
        env = att.get("environment")
        for d in att["declarations"]:
            if not isinstance(d, dict):
                raise ValueError(f"{ap}: declaration entry is not an object")
            name = d.get("name")
            if not name:
                raise ValueError(f"{ap}: declaration missing name")
            axl = att.get("module_verified") and d.get("axle_verdict") == "verified"
            axioms = d.get("axioms") or []
            facts = DeclFacts(
                name=name, kind=d.get("kind", "theorem"),
                axioms=axioms,
                flags=Flags(native_decide=d.get("native_decide", False)),
                axle_verified=True if axl else (False if d.get("axle_verdict") == "failed" else None),
            )
            prov = _provenance_for(module, name, verdicts)
            if prov.get("kind_override") is not None:
                facts.kind = prov["kind_override"]
            facts.conditional_rung = prov.get("conditional_rung")
            entries.append(build_entry(
                facts, prov,
                # The attestation stem is tied to the root import and therefore
                # identifies the actual source file.  Namespace tails do not:
                # e.g. `Brockian.BrocardGap` lives in
                # `Brockian/BrocardGapConjecture.lean`.
                source={"file": f"Brockian/{stem}.lean"},
                statement=d.get("statement", ""), axle_env=env))
    entries.sort(key=lambda e: (e["module"], e["name"]))
    # DISCHARGED post-pass: a CONDITIONAL whose `discharged_by` names a PROVED theorem in-core
    # (its hypothesis/conclusion is now proved elsewhere) is reclassified DISCHARGED — no longer
    # open frontier, but distinct from PROVED since it is a conditional-form lemma. Honest count:
    # DISCHARGED is NOT counted as an open conditional and NOT as an unconditional PROVED.
    # discharged_by is resolved UNAMBIGUOUSLY: either a fully-qualified PROVED name,
    # or a short name matching exactly ONE PROVED entry across the whole registry.
    # A colliding short name (same short name in several PROVED modules) must NOT
    # discharge anything — it stays CONDITIONAL with a stderr warning.
    full_names = {e["name"] for e in entries if e["register"] == "PROVED"}
    by_short: dict[str, set[str]] = defaultdict(set)
    for n in full_names:
        by_short[n.split(".")[-1]].add(n)
    for e in entries:
        db = e.get("discharged_by")
        if e["register"] != "CONDITIONAL" or not db:
            continue
        if db in full_names or len(by_short.get(db, ())) == 1:
            e["register"] = "DISCHARGED"
        elif len(by_short.get(db, ())) > 1:
            print(
                f"WARNING: {e['name']}: discharged_by {db!r} is ambiguous among PROVED "
                f"theorems {sorted(by_short[db])}; leaving CONDITIONAL",
                file=sys.stderr,
            )
    by_reg: dict[str, int] = {}
    for e in entries:
        by_reg[e["register"]] = by_reg.get(e["register"], 0) + 1
    return {"generated_from": "AXLE attestations", "summary": by_reg, "theorems": entries}


def render_markdown(reg: dict[str, Any]) -> str:
    lines = ["# Brockian Verified-Theorem Registry", "",
             "> Generated from AXLE independent verification attestations. "
             "`register` is derived from axioms + AXLE verdict, never hand-asserted (spec §5).", "",
             "> **PROVED** includes theorems closed by the kernel-checked `decide` tactic "
             "(finite `ZMod`/`Finset` checks — genuinely verified, ledger-consistent). "
             "`native_decide` (compiler-trusted, adds `Lean.ofReduceBool`) is excluded from "
             "PROVED by the axiom gate. `DEFINITION` = a supporting `def`; `CONJECTURE` = a "
             "named Prop container (never a claim).", "",
             "## Summary", ""]
    for k, v in sorted(reg["summary"].items()):
        lines.append(f"- **{k}**: {v}")
    lines += ["", "## Theorems", "",
              "| Register | Name | Axioms clean | AXLE | Env | Ledger |",
              "|---|---|---|---|---|---|"]
    for e in reg["theorems"]:
        ax = "✓" if e["verification"]["axioms_ok"] else "—"
        av = e["verification"]["axle"]["verdict"]
        env = e["verification"]["axle"]["environment"] or ""
        lines.append(f"| {e['register']} | `{e['name']}` | {ax} | {av} | {env} | {e.get('ledger_run') or ''} |")
    return "\n".join(lines) + "\n"


def main() -> int:
    import os
    reg = generate("registry/attestations", "provenance/verdicts.yaml")
    os.makedirs("registry", exist_ok=True)
    json.dump(reg, open("registry/theorems.json", "w"), indent=2)
    open("REGISTRY.md", "w").write(render_markdown(reg))
    print(f"registry: {reg['summary']} -> registry/theorems.json + REGISTRY.md")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
