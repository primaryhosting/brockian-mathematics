#!/usr/bin/env python3
"""Read-only overclaim firewall audit for the Brockian registry.

The registry does not currently record Lean's full transitive dependency graph.
This script therefore performs a conservative text/provenance audit:

  * direct references from PROVED entries to open declaration names;
  * references from PROVED entries to modules containing open declarations;
  * mixed modules that contain both PROVED and CONDITIONAL/CONJECTURE entries.

It never rewrites registry outputs and should be treated as a warning generator,
not as a proof of dependency independence.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import textwrap
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any


OPEN_REGISTERS = {"CONDITIONAL", "CONJECTURE"}
DEFAULT_CONTEXT_FIELDS = (
    "name",
    "module",
    "statement",
    "ledger_run",
    "provenance_note",
    "conditional_rung",
)


@dataclass(frozen=True)
class Finding:
    severity: str
    kind: str
    proved_name: str
    open_name: str
    detail: str


def load_registry(path: Path) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    with path.open(encoding="utf-8") as f:
        registry = json.load(f)
    if not isinstance(registry, dict):
        raise ValueError(f"{path}: expected a JSON object")
    entries = registry.get("theorems")
    if not isinstance(entries, list):
        raise ValueError(f"{path}: expected key 'theorems' with a list value")
    typed_entries = [e for e in entries if isinstance(e, dict)]
    return registry, typed_entries


def strip_yaml_quotes(value: str) -> str:
    value = value.strip()
    if len(value) >= 2 and value[0] == value[-1] and value[0] in {"'", '"'}:
        return value[1:-1]
    return value


def load_provenance_contexts(path: Path) -> tuple[dict[str, str], str | None]:
    """Parse the small subset of provenance/verdicts.yaml used by this audit.

    This is deliberately stdlib-only. It recognizes run-level `module`,
    `ledger_run`, and `provenance_note`, plus one-level `overrides` with `name`,
    `ledger_run`, `provenance_note`, and `conditional_rung`. If the YAML grows
    beyond that shape, the embedded registry fields still carry the audit.
    """
    if not path.exists():
        return {}, f"{path}: missing; using registry-embedded provenance only"

    contexts: dict[str, str] = {}
    current_module: str | None = None
    current_run_fields: dict[str, str] = {}
    current_override: dict[str, str] | None = None
    in_overrides = False

    def flush_override() -> None:
        nonlocal current_override
        if current_module and current_override and current_override.get("name"):
            full_name = f"{current_module}.{current_override['name']}"
            text_parts = [
                current_run_fields.get("ledger_run"),
                current_run_fields.get("provenance_note"),
                current_override.get("ledger_run"),
                current_override.get("provenance_note"),
                current_override.get("conditional_rung"),
            ]
            contexts[full_name] = " ".join(p for p in text_parts if p)
        current_override = None

    def flush_run() -> None:
        flush_override()
        if current_module:
            text_parts = [
                current_run_fields.get("ledger_run"),
                current_run_fields.get("provenance_note"),
                current_run_fields.get("conditional_rung"),
            ]
            contexts[f"module:{current_module}"] = " ".join(p for p in text_parts if p)

    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as exc:
        return {}, f"{path}: could not read provenance YAML ({exc})"

    for raw in lines:
        line = raw.split("#", 1)[0].rstrip()
        if not line.strip():
            continue
        indent = len(line) - len(line.lstrip(" "))
        stripped = line.strip()

        if indent == 2 and stripped.endswith(":") and not stripped.startswith("- "):
            flush_run()
            current_module = None
            current_run_fields = {}
            current_override = None
            in_overrides = False
            continue

        if indent == 4 and ":" in stripped and current_override is None:
            key, value = stripped.split(":", 1)
            key = key.strip()
            value = strip_yaml_quotes(value)
            if key == "module":
                current_module = value
            elif key in {"ledger_run", "provenance_note", "conditional_rung"}:
                current_run_fields[key] = value
            elif key == "overrides":
                in_overrides = True
            continue

        if indent == 6 and in_overrides and stripped.startswith("- "):
            flush_override()
            current_override = {}
            item = stripped[2:]
            if ":" in item:
                key, value = item.split(":", 1)
                current_override[key.strip()] = strip_yaml_quotes(value)
            continue

        if indent >= 8 and in_overrides and current_override is not None and ":" in stripped:
            key, value = stripped.split(":", 1)
            current_override[key.strip()] = strip_yaml_quotes(value)
            continue

        # Unknown YAML fragments are intentionally ignored by this lightweight
        # parser; registry-embedded provenance remains the authoritative input.
        continue

    flush_run()
    return contexts, None


def entry_name(entry: dict[str, Any]) -> str:
    return str(entry.get("name") or "")


def short_name(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def entry_text(entry: dict[str, Any], contexts: dict[str, str]) -> str:
    parts: list[str] = []
    for field in DEFAULT_CONTEXT_FIELDS:
        value = entry.get(field)
        if value is not None:
            parts.append(str(value))
    source = entry.get("source")
    if isinstance(source, dict):
        parts.extend(str(v) for v in source.values() if v is not None)
    name = entry_name(entry)
    module = str(entry.get("module") or "")
    if name in contexts:
        parts.append(contexts[name])
    if module and f"module:{module}" in contexts:
        parts.append(contexts[f"module:{module}"])
    return "\n".join(parts)


def token_pattern(token: str) -> re.Pattern[str]:
    return re.compile(rf"(?<![A-Za-z0-9_'.]){re.escape(token)}(?![A-Za-z0-9_'])")


def mentions(token: str, text: str) -> bool:
    return bool(token and token_pattern(token).search(text))


def module_prefixes(module: str) -> list[str]:
    parts = module.split(".")
    return [".".join(parts[:i]) for i in range(2, len(parts))]


def collect_findings(
    entries: list[dict[str, Any]], contexts: dict[str, str]
) -> tuple[list[Finding], dict[str, list[dict[str, Any]]]]:
    proved_entries = [e for e in entries if e.get("register") == "PROVED"]
    open_entries = [e for e in entries if e.get("register") in OPEN_REGISTERS]

    open_by_module: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for entry in open_entries:
        open_by_module[str(entry.get("module") or "")].append(entry)

    findings: list[Finding] = []
    for proved in proved_entries:
        proved_name = entry_name(proved)
        proved_module = str(proved.get("module") or "")
        text = entry_text(proved, contexts)

        for open_entry in open_entries:
            open_name = entry_name(open_entry)
            open_short = short_name(open_name)
            open_module = str(open_entry.get("module") or "")
            if open_name == proved_name:
                continue

            if mentions(open_name, text):
                findings.append(
                    Finding(
                        "HIGH",
                        "direct-open-name",
                        proved_name,
                        open_name,
                        f"PROVED provenance/metadata mentions open declaration {open_name}",
                    )
                )
                continue

            if len(open_short) >= 8 and mentions(open_short, text):
                findings.append(
                    Finding(
                        "HIGH",
                        "direct-open-short-name",
                        proved_name,
                        open_name,
                        f"PROVED provenance/metadata mentions open short name {open_short}",
                    )
                )
                continue

            if open_module and open_module != proved_module and mentions(open_module, text):
                findings.append(
                    Finding(
                        "MEDIUM",
                        "open-module-reference",
                        proved_name,
                        open_name,
                        f"PROVED provenance/metadata mentions open-bearing module {open_module}",
                    )
                )

        for open_entry in open_by_module.get(proved_module, []):
            open_name = entry_name(open_entry)
            if open_name == proved_name:
                continue
            findings.append(
                Finding(
                    "LOW",
                    "mixed-module",
                    proved_name,
                    open_name,
                    "same module contains both PROVED and open entries; inspect imports/provenance before citing the proved entry as independent",
                )
            )

        for prefix in module_prefixes(proved_module):
            for open_entry in open_by_module.get(prefix, []):
                findings.append(
                    Finding(
                        "LOW",
                        "parent-module-open",
                        proved_name,
                        entry_name(open_entry),
                        f"proved entry is in submodule of open-bearing parent module {prefix}",
                    )
                )

    return findings, open_by_module


def summarize(entries: list[dict[str, Any]]) -> Counter[str]:
    return Counter(str(e.get("register") or "UNKNOWN") for e in entries)


def print_wrapped(prefix: str, text: str, width: int = 100) -> None:
    lines = textwrap.wrap(
        text,
        width=width,
        initial_indent=prefix,
        subsequent_indent=" " * len(prefix),
        break_long_words=False,
        break_on_hyphens=False,
    )
    for line in lines or [prefix.rstrip()]:
        print(line)


def print_report(
    registry_path: Path,
    provenance_path: Path,
    entries: list[dict[str, Any]],
    contexts: dict[str, str],
    provenance_warning: str | None,
    findings: list[Finding],
    max_findings: int,
) -> None:
    counts = summarize(entries)
    by_severity = Counter(f.severity for f in findings)
    by_kind = Counter(f.kind for f in findings)
    open_entries = [e for e in entries if e.get("register") in OPEN_REGISTERS]

    print("Dependency firewall audit")
    print(f"  registry: {registry_path}")
    print(f"  provenance: {provenance_path}")
    print(f"  entries: {len(entries)}")
    for key in ["PROVED", "DEFINITION", "CONDITIONAL", "CONJECTURE", "COMPUTATION", "UNVERIFIED"]:
        if key in counts:
            print(f"  {key}: {counts[key]}")
    print(f"  provenance contexts loaded: {len(contexts)}")
    if provenance_warning:
        print(f"  warning: {provenance_warning}")
    print()

    print("Open entries")
    if not open_entries:
        print("  none")
    else:
        for entry in sorted(open_entries, key=lambda e: entry_name(e)):
            print(f"  - {entry.get('register')} {entry_name(entry)}")
    print()

    print("Firewall findings")
    if not findings:
        print("  PASS: no PROVED entry cited an open declaration/module under this conservative audit.")
        print()
        return

    print(f"  total: {len(findings)}")
    for severity in ["HIGH", "MEDIUM", "LOW"]:
        if by_severity[severity]:
            print(f"  {severity}: {by_severity[severity]}")
    for kind, count in sorted(by_kind.items()):
        print(f"  {kind}: {count}")
    print()

    print(f"First {min(max_findings, len(findings))} findings")
    ordered = sorted(
        findings,
        key=lambda f: (
            {"HIGH": 0, "MEDIUM": 1, "LOW": 2}.get(f.severity, 9),
            f.kind,
            f.proved_name,
            f.open_name,
        ),
    )
    for finding in ordered[:max_findings]:
        print(f"- [{finding.severity}] {finding.kind}")
        print_wrapped("  proved: ", finding.proved_name)
        print_wrapped("  open: ", finding.open_name)
        print_wrapped("  detail: ", finding.detail)
    if len(findings) > max_findings:
        print(f"... {len(findings) - max_findings} additional findings hidden; rerun with --max-findings.")
    print()


def main(argv: list[str] | None = None) -> int:
    repo = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(
        description="Conservative read-only audit for PROVED entries that cite open registry nodes."
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
    parser.add_argument(
        "--max-findings",
        type=int,
        default=60,
        help="maximum detailed findings to print",
    )
    parser.add_argument(
        "--fail-on-high",
        action="store_true",
        help="exit nonzero if a HIGH severity direct open-declaration citation is found",
    )
    args = parser.parse_args(argv)

    _registry, entries = load_registry(args.registry)
    contexts, provenance_warning = load_provenance_contexts(args.provenance)
    findings, _open_by_module = collect_findings(entries, contexts)
    print_report(
        args.registry,
        args.provenance,
        entries,
        contexts,
        provenance_warning,
        findings,
        max(0, args.max_findings),
    )

    if args.fail_on_high and any(f.severity == "HIGH" for f in findings):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
