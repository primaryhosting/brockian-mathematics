#!/usr/bin/env python3
"""Fail when registry/theorems.json is stale relative to its generated inputs."""
from __future__ import annotations

from collections import Counter
import json
import os
from pathlib import Path
import sys
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from scripts.gen_registry import generate  # noqa: E402


REGISTRY_PATH = REPO_ROOT / "registry" / "theorems.json"
ATTEST_DIR = REPO_ROOT / "registry" / "attestations"
VERDICTS_PATH = REPO_ROOT / "provenance" / "verdicts.yaml"


def _canonical(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def _load_registry(path: Path) -> dict[str, Any]:
    try:
        with path.open() as f:
            return json.load(f)
    except FileNotFoundError:
        print(f"{path.relative_to(REPO_ROOT)} is missing")
        raise SystemExit(1)


def _entry_name(canonical_entry: str) -> str:
    try:
        return json.loads(canonical_entry).get("name", "<unnamed>")
    except json.JSONDecodeError:
        return "<invalid>"


def _compare_entries(expected: list[dict[str, Any]], actual: list[dict[str, Any]]) -> list[str]:
    expected_counts = Counter(_canonical(entry) for entry in expected)
    actual_counts = Counter(_canonical(entry) for entry in actual)
    missing = expected_counts - actual_counts
    extra = actual_counts - expected_counts

    if not missing and not extra:
        return []

    lines = [
        f"theorems differ: missing {sum(missing.values())}, extra {sum(extra.values())}",
    ]
    if len(expected) != len(actual):
        lines.append(f"theorem count: generated {len(expected)}, file {len(actual)}")
    if missing:
        sample = next(iter(missing))
        lines.append(f"first missing generated entry: {_entry_name(sample)}")
    if extra:
        sample = next(iter(extra))
        lines.append(f"first extra file entry: {_entry_name(sample)}")
    return lines


def main() -> int:
    os.chdir(REPO_ROOT)
    actual = _load_registry(REGISTRY_PATH)
    expected = generate(str(ATTEST_DIR), str(VERDICTS_PATH))

    messages: list[str] = []
    if actual.get("summary") != expected.get("summary"):
        messages.append(
            f"summary differs: generated {expected.get('summary')}, file {actual.get('summary')}"
        )
    messages.extend(
        _compare_entries(
            expected.get("theorems") or [],
            actual.get("theorems") or [],
        )
    )

    if messages:
        print("registry/theorems.json is stale")
        for message in messages:
            print(f"- {message}")
        print("Run: python3 scripts/gen_registry.py")
        return 1

    print(
        "registry/theorems.json is fresh "
        f"({len(actual.get('theorems') or [])} entries; summary {actual.get('summary')})"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
