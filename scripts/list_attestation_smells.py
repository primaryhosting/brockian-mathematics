#!/usr/bin/env python3
"""List noncanonical attestation smells without modifying the repo.

The Brockian registry is intentionally generated from root-imported modules.
This helper reports attestation files whose filename does not line up with
that integration rule, especially short-name duplicates such as
`FourierMultiplier.json` beside canonical `WeylFourierMultiplier.json`.
"""
from __future__ import annotations

import argparse
import json
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any


@dataclass(frozen=True)
class Attestation:
    path: Path
    stem: str
    module: str
    module_verified: bool | None
    declaration_count: int | None


def load_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        data = json.load(handle)
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected JSON object")
    return data


def load_attestation(path: Path) -> Attestation:
    data = load_json(path)
    declarations = data.get("declarations")
    return Attestation(
        path=path,
        stem=path.stem,
        module=str(data.get("module", "")),
        module_verified=data.get("module_verified")
        if isinstance(data.get("module_verified"), bool)
        else None,
        declaration_count=len(declarations) if isinstance(declarations, list) else None,
    )


def root_import_stems(path: Path) -> set[str]:
    stems: set[str] = set()
    if not path.exists():
        return stems
    for line in path.read_text(encoding="utf-8").splitlines():
        stripped = line.strip()
        if stripped.startswith("import Brockian."):
            stems.add(stripped.removeprefix("import Brockian."))
    return stems


def shell_quote_path(path: Path) -> str:
    text = str(path)
    return "'" + text.replace("'", "'\"'\"'") + "'"


def canonical_for_group(group: list[Attestation], imported: set[str]) -> Attestation | None:
    imported_members = [att for att in group if att.stem in imported]
    verified_imported = [att for att in imported_members if att.module_verified is True]
    if verified_imported:
        return sorted(verified_imported, key=lambda att: att.path.name)[0]
    if imported_members:
        return sorted(imported_members, key=lambda att: att.path.name)[0]
    verified = [att for att in group if att.module_verified is True]
    if verified:
        return sorted(verified, key=lambda att: att.path.name)[0]
    return sorted(group, key=lambda att: att.path.name)[0] if group else None


def main() -> int:
    repo = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=repo / "Brockian.lean")
    parser.add_argument(
        "--attestations",
        type=Path,
        default=repo / "registry" / "attestations",
    )
    parser.add_argument(
        "--show-clean",
        action="store_true",
        help="also print attestation groups with no detected smell",
    )
    args = parser.parse_args()

    imported = root_import_stems(args.root)
    attestations = [
        load_attestation(path)
        for path in sorted(args.attestations.glob("*.json"))
    ]
    attest_stems = {att.stem for att in attestations}

    by_module: dict[str, list[Attestation]] = defaultdict(list)
    for att in attestations:
        by_module[att.module].append(att)

    short_duplicates: list[tuple[Attestation, Attestation]] = []
    duplicate_groups: list[tuple[str, Attestation | None, list[Attestation]]] = []
    for module, group in sorted(by_module.items()):
        if len(group) <= 1:
            continue
        canonical = canonical_for_group(group, imported)
        duplicate_groups.append((module, canonical, group))
        for att in sorted(group, key=lambda item: item.path.name):
            if canonical is not None and att.path != canonical.path:
                short_duplicates.append((att, canonical))

    attest_not_imported = sorted(
        (att for att in attestations if att.stem not in imported),
        key=lambda att: att.path.name,
    )
    imports_without_attestation = sorted(imported - attest_stems)
    unverified = sorted(
        (att for att in attestations if att.module_verified is not True),
        key=lambda att: att.path.name,
    )

    print("Attestation smell report")
    print(f"  root imports: {args.root}")
    print(f"  attestations: {args.attestations}")
    print(f"  attestation files: {len(attestations)}")
    print(f"  root-imported stems: {len(imported)}")
    print()

    print("Duplicate attestation modules")
    if duplicate_groups:
        for module, canonical, group in duplicate_groups:
            canonical_name = canonical.path.name if canonical else "<none>"
            print(f"- {module}")
            print(f"  canonical candidate: {canonical_name}")
            for att in sorted(group, key=lambda item: item.path.name):
                markers = []
                if att.stem in imported:
                    markers.append("root-import stem")
                if canonical is not None and att.path == canonical.path:
                    markers.append("canonical")
                if att.module_verified is not True:
                    markers.append(f"module_verified={att.module_verified!r}")
                suffix = f" ({', '.join(markers)})" if markers else ""
                print(f"  - {att.path.name}{suffix}")
    else:
        print("  none")
    print()

    print("Noncanonical short-name duplicates")
    if short_duplicates:
        for duplicate, canonical in short_duplicates:
            print(f"- {duplicate.path.name} duplicates {canonical.path.name}")
            print(f"  module: {duplicate.module}")
            print(f"  duplicate verified: {duplicate.module_verified!r}")
            print(f"  canonical verified: {canonical.module_verified!r}")
            print(f"  review: diff -u {shell_quote_path(canonical.path)} {shell_quote_path(duplicate.path)}")
            print(f"  cleanup: rm -- {shell_quote_path(duplicate.path)}")
    else:
        print("  none")
    print()

    print("Attestations not imported by Brockian.lean")
    if attest_not_imported:
        for att in attest_not_imported:
            print(f"- {att.path.name}: module={att.module}, verified={att.module_verified!r}")
    else:
        print("  none")
    print()

    print("Root imports without same-stem attestation")
    if imports_without_attestation:
        for stem in imports_without_attestation:
            print(f"- {stem}")
    else:
        print("  none")
    print()

    print("Unverified attestation files")
    if unverified:
        for att in unverified:
            print(f"- {att.path.name}: module={att.module}, module_verified={att.module_verified!r}")
    else:
        print("  none")
    print()

    if args.show_clean:
        print("Clean single-file attestation modules")
        for module, group in sorted(by_module.items()):
            if len(group) == 1 and group[0].stem in imported and group[0].module_verified is True:
                print(f"- {group[0].path.name}: {module}")
        print()

    smell_count = (
        len(short_duplicates)
        + len(attest_not_imported)
        + len(imports_without_attestation)
        + len(unverified)
    )
    print("Summary")
    print(f"  duplicate module groups: {len(duplicate_groups)}")
    print(f"  short-name duplicates: {len(short_duplicates)}")
    print(f"  non-root attestations: {len(attest_not_imported)}")
    print(f"  root imports without same-stem attestation: {len(imports_without_attestation)}")
    print(f"  unverified attestations: {len(unverified)}")
    print(f"  total reported smells: {smell_count}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
