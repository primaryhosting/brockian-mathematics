#!/usr/bin/env python3
"""Audit open registry entries for stale or superseded targets.

Reads only:
  - registry/theorems.json
  - provenance/verdicts.yaml

This is intentionally read-only: it does not regenerate or rewrite registry outputs.
"""
from __future__ import annotations

import argparse
import json
import re
import textwrap
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


OPEN_REGISTERS = {"CONJECTURE", "CONDITIONAL"}
SUMMARY_ORDER = [
    "PROVED",
    "CONDITIONAL",
    "CONJECTURE",
    "DEFINITION",
    "COMPUTATION",
    "UNVERIFIED",
]


def short_name(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as f:
        data = json.load(f)
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected a JSON object")
    return data


def load_yaml(path: Path) -> tuple[dict[str, Any], str | None]:
    try:
        import yaml  # type: ignore[import-not-found]
    except ModuleNotFoundError:
        return {}, "PyYAML is unavailable; provenance YAML was not loaded."

    if not path.exists():
        return {}, f"{path}: missing; provenance YAML was not loaded."

    with path.open(encoding="utf-8") as f:
        data = yaml.safe_load(f) or {}
    if not isinstance(data, dict):
        return {}, f"{path}: expected a YAML mapping; provenance YAML was not loaded."
    return data, None


def registry_summary(entries: list[dict[str, Any]]) -> Counter[str]:
    return Counter(str(e.get("register", "UNKNOWN")) for e in entries)


def ordered_keys(counter: Counter[str]) -> list[str]:
    seen = set()
    keys = []
    for key in SUMMARY_ORDER:
        if key in counter:
            keys.append(key)
            seen.add(key)
    for key in sorted(counter):
        if key not in seen:
            keys.append(key)
    return keys


def verification_line(entry: dict[str, Any]) -> str:
    verification = entry.get("verification") or {}
    axle = verification.get("axle") or {}
    verdict = axle.get("verdict") or "unknown"
    env = axle.get("environment")
    return f"{verdict} {env}" if env else str(verdict)


def provenance_contexts(verdicts: dict[str, Any]) -> dict[str, dict[str, Any]]:
    """Mimic gen_registry.py's module/default plus per-declaration override lookup."""
    contexts: dict[str, dict[str, Any]] = {}
    for run_id, run in (verdicts.get("runs") or {}).items():
        if not isinstance(run, dict):
            continue
        module = run.get("module")
        if not module:
            continue
        run_context = {
            "run_id": str(run_id),
            "module": module,
            "run_ledger": run.get("ledger_run"),
            "run_note": run.get("provenance_note"),
            "run_rung": run.get("conditional_rung"),
        }
        for override in run.get("overrides") or []:
            if not isinstance(override, dict) or not override.get("name"):
                continue
            full_name = f"{module}.{override['name']}"
            context = dict(run_context)
            context.update(
                {
                    "override_ledger": override.get("ledger_run"),
                    "override_note": override.get("provenance_note"),
                    "override_rung": override.get("conditional_rung"),
                }
            )
            contexts[full_name] = context
    return contexts


def provenance_text(entry: dict[str, Any], contexts: dict[str, dict[str, Any]]) -> str:
    context = contexts.get(str(entry.get("name")), {})
    fields = [
        entry.get("ledger_run"),
        entry.get("provenance_note"),
        context.get("run_ledger"),
        context.get("run_note"),
        context.get("override_ledger"),
        context.get("override_note"),
    ]
    return " ".join(str(x) for x in fields if x)


def identifier_tokens(name: str) -> list[str]:
    name = short_name(name)
    snake = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", name)
    return [tok.lower() for tok in re.split(r"[^A-Za-z0-9]+", snake) if tok]


def normalized_identifier(name: str) -> str:
    return "".join(identifier_tokens(name))


def strip_proof_words(tokens: list[str]) -> list[str]:
    proof_words = {
        "theorem",
        "lemma",
        "proof",
        "proved",
        "verified",
        "holds",
        "true",
    }
    return [tok for tok in tokens if tok not in proof_words]


def normalized_statement(statement: str | None) -> str:
    if not statement:
        return ""
    return re.sub(r"\s+", " ", statement).strip().lower()


def is_same_target(open_entry: dict[str, Any], proved_entry: dict[str, Any]) -> str | None:
    open_statement = normalized_statement(open_entry.get("statement"))
    proved_statement = normalized_statement(proved_entry.get("statement"))
    if open_statement and open_statement == proved_statement:
        return "same normalized statement"

    open_short = short_name(str(open_entry.get("name", "")))
    proved_short = short_name(str(proved_entry.get("name", "")))
    open_norm = normalized_identifier(open_short)
    proved_norm = normalized_identifier(proved_short)
    proved_base = "".join(strip_proof_words(identifier_tokens(proved_short)))

    if open_norm and open_norm == proved_base:
        return "proved name matches open target name"
    for suffix in ("proof", "proved", "verified", "theorem", "holds", "true"):
        if proved_norm == open_norm + suffix:
            return f"proved name is open target plus '{suffix}'"
    return None


def target_container_findings(
    open_entries: list[dict[str, Any]], proved_entries: list[dict[str, Any]]
) -> list[tuple[dict[str, Any], dict[str, Any], str]]:
    proved_by_module: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for entry in proved_entries:
        proved_by_module[str(entry.get("module", ""))].append(entry)

    findings = []
    for entry in open_entries:
        if entry.get("register") != "CONJECTURE" and entry.get("kind") not in {
            "conjecture",
            "def",
            "abbrev",
        }:
            continue
        for proved in proved_by_module.get(str(entry.get("module", "")), []):
            reason = is_same_target(entry, proved)
            if reason:
                findings.append((entry, proved, reason))
    return findings


def name_is_mentioned(name: str, text: str) -> bool:
    if not text:
        return False
    escaped = re.escape(name)
    return re.search(rf"(?<![A-Za-z0-9_]){escaped}(?![A-Za-z0-9_])", text) is not None


def mentioned_proved_findings(
    open_entries: list[dict[str, Any]],
    proved_entries: list[dict[str, Any]],
    contexts: dict[str, dict[str, Any]],
) -> list[tuple[dict[str, Any], list[dict[str, Any]], list[dict[str, Any]]]]:
    findings = []
    for entry in open_entries:
        if entry.get("register") != "CONDITIONAL":
            continue
        text = provenance_text(entry, contexts)
        same_module = []
        external = []
        for proved in proved_entries:
            full = str(proved.get("name", ""))
            short = short_name(full)
            if len(short) < 5:
                continue
            if name_is_mentioned(full, text) or name_is_mentioned(short, text):
                if proved.get("module") == entry.get("module"):
                    same_module.append(proved)
                else:
                    external.append(proved)
        if same_module or external:
            findings.append((entry, same_module, external))
    return findings


def wrap_line(label: str, value: Any, width: int = 100) -> list[str]:
    text = "" if value is None else str(value)
    prefix = f"  {label}: "
    if not text:
        return [prefix.rstrip()]
    return textwrap.wrap(
        text,
        width=width,
        initial_indent=prefix,
        subsequent_indent=" " * len(prefix),
        break_long_words=False,
        break_on_hyphens=False,
    )


def print_summary(registry: dict[str, Any], entries: list[dict[str, Any]]) -> None:
    recounted = registry_summary(entries)
    declared = Counter({str(k): int(v) for k, v in (registry.get("summary") or {}).items()})
    print("Current summary")
    print(f"  total entries: {len(entries)}")
    for key in ordered_keys(recounted):
        print(f"  {key}: {recounted[key]}")
    if declared and declared != recounted:
        print("  warning: embedded summary differs from the theorem list recount")
    print()


def print_open_entries(open_entries: list[dict[str, Any]]) -> None:
    print("CONJECTURE and CONDITIONAL entries")
    if not open_entries:
        print("  none")
        print()
        return
    for entry in open_entries:
        print(f"- {entry.get('register')} {entry.get('name')}")
        print(f"  kind: {entry.get('kind')}")
        print(f"  module: {entry.get('module')}")
        source = entry.get("source") or {}
        if source.get("file"):
            print(f"  source: {source.get('file')}")
        if entry.get("conditional_rung"):
            print(f"  conditional_rung: {entry.get('conditional_rung')}")
        print(f"  axle: {verification_line(entry)}")
        if entry.get("ledger_run"):
            for line in wrap_line("ledger", entry.get("ledger_run")):
                print(line)
        if entry.get("provenance_note"):
            for line in wrap_line("note", entry.get("provenance_note")):
                print(line)
    print()


def print_stale_findings(
    target_findings: list[tuple[dict[str, Any], dict[str, Any], str]],
    mentioned_findings: list[tuple[dict[str, Any], list[dict[str, Any]], list[dict[str, Any]]]],
    yaml_warning: str | None,
) -> None:
    print("Likely stale open items")
    print("  Target Prop containers with a matching PROVED theorem:")
    if target_findings:
        for open_entry, proved_entry, reason in target_findings:
            print(f"  - {open_entry.get('name')}")
            print(f"    matched: {proved_entry.get('name')}")
            print(f"    reason: {reason}")
    else:
        print("  - none detected")

    print("  Conditionals with citable PROVED entries mentioned in provenance:")
    if yaml_warning:
        print(f"  - note: {yaml_warning} Using registry-embedded provenance fields only.")
    if mentioned_findings:
        for entry, same_module, external in mentioned_findings:
            print(f"  - {entry.get('name')}")
            if same_module:
                names = ", ".join(short_name(str(e.get("name"))) for e in same_module)
                for line in wrap_line("same-module", names):
                    print("  " + line)
            if external:
                names = ", ".join(str(e.get("name")) for e in external)
                for line in wrap_line("external", names):
                    print("  " + line)
    else:
        print("  - none detected")
    print()


def main() -> int:
    repo = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(
        description="Audit registry open entries without regenerating registry outputs."
    )
    parser.add_argument(
        "--registry",
        type=Path,
        default=repo / "registry" / "theorems.json",
        help="path to registry/theorems.json",
    )
    parser.add_argument(
        "--provenance",
        type=Path,
        default=repo / "provenance" / "verdicts.yaml",
        help="path to provenance/verdicts.yaml",
    )
    args = parser.parse_args()

    registry = load_json(args.registry)
    entries = registry.get("theorems") or []
    if not isinstance(entries, list):
        raise ValueError(f"{args.registry}: expected 'theorems' to be a list")

    verdicts, yaml_warning = load_yaml(args.provenance)
    contexts = provenance_contexts(verdicts) if verdicts else {}

    open_entries = [
        e for e in entries if str(e.get("register")) in OPEN_REGISTERS
    ]
    open_entries.sort(key=lambda e: (str(e.get("module", "")), str(e.get("name", ""))))
    proved_entries = [e for e in entries if e.get("register") == "PROVED"]

    print("Registry open-item audit")
    print(f"  registry: {args.registry}")
    print(f"  provenance: {args.provenance}")
    if yaml_warning:
        print(f"  warning: {yaml_warning}")
    print()

    print_summary(registry, entries)
    print_open_entries(open_entries)
    print_stale_findings(
        target_container_findings(open_entries, proved_entries),
        mentioned_proved_findings(open_entries, proved_entries, contexts),
        yaml_warning,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
