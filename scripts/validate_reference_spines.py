"""Validate theorem-ingestion manifests under ``provenance/reference-spines``.

The reference-spine format keeps three boundaries machine-checkable:

* externally sourced classical mathematics is not counted as Brockian novelty;
* registry-backed declarations really resolve to green registry entries;
* new Lean source may be marked pending AXLE, but a manifest cannot promote it.

The validator intentionally uses a small explicit schema rather than silently accepting
arbitrary YAML. Run it from the repository root:

    python3 scripts/validate_reference_spines.py
"""
from __future__ import annotations

import argparse
import copy
import glob
import json
import re
from pathlib import Path
from typing import Any

import yaml


REPO = Path(__file__).resolve().parents[1]
DEFAULT_GLOB = "provenance/reference-spines/*.yaml"
REGISTRY = REPO / "registry" / "theorems.json"

REQUIRED_TAGS = {
    "CLASSICAL_REFERENCE",
    "BROCKIAN_BRIDGE",
    "BROCKIAN_RESULT",
    "EMPIRICAL_COMPUTATION",
}
EXCLUDED_FROM_NOVELTY = {
    "CLASSICAL_REFERENCE",
    "BROCKIAN_BRIDGE",
    "EMPIRICAL_COMPUTATION",
}
VALID_STATUSES = {
    "registry_verified",
    "lean_source_pending_axle",
    "queued",
    "documented_empirical",
}
GREEN_REGISTERS = {"PROVED", "DEFINITION", "DISCHARGED"}
DECL_RE_TEMPLATE = (
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev|structure|class|inductive)\s+"
    r"(?:[A-Za-z_][\w'.]*\.)?{name}(?![\w'])"
)


def load_registry(path: Path = REGISTRY) -> dict[str, str]:
    doc = json.loads(path.read_text(encoding="utf-8"))
    return {item["name"]: item["register"] for item in doc.get("theorems", [])}


def _source_files(item: dict[str, Any]) -> list[str]:
    files = item.get("source_files")
    if files is None and item.get("source_file") is not None:
        files = [item["source_file"]]
    return files if isinstance(files, list) else []


def _repo_file(rel: str) -> Path | None:
    if not isinstance(rel, str):
        return None
    path = (REPO / rel).resolve()
    try:
        path.relative_to(REPO)
    except ValueError:
        return None
    return path if path.is_file() else None


def _declaration_exists(name: str, files: list[str]) -> bool:
    short = name.rsplit(".", 1)[-1]
    pattern = re.compile(DECL_RE_TEMPLATE.format(name=re.escape(short)), re.MULTILINE)
    for rel in files:
        path = _repo_file(rel)
        if path is not None and pattern.search(path.read_text(encoding="utf-8")):
            return True
    return False


def validate_document(doc: dict[str, Any], registry: dict[str, str], label: str) -> list[str]:
    errors: list[str] = []

    def err(message: str) -> None:
        errors.append(f"{label}: {message}")

    if doc.get("schema_version") != 1:
        err("schema_version must be 1")
    if not isinstance(doc.get("spine_id"), str) or not doc["spine_id"]:
        err("spine_id must be a non-empty string")

    source = doc.get("source")
    page_count: int | None = None
    if not isinstance(source, dict):
        err("source must be a mapping")
    else:
        digest = source.get("pdf_sha256", "")
        if not isinstance(digest, str) or re.fullmatch(r"[0-9a-f]{64}", digest) is None:
            err("source.pdf_sha256 must be a lowercase SHA-256 digest")
        pages = source.get("page_count")
        if not isinstance(pages, int) or pages <= 0:
            err("source.page_count must be a positive integer")
        else:
            page_count = pages

    tags = doc.get("classification_tags")
    if not isinstance(tags, dict) or set(tags) != REQUIRED_TAGS:
        err(f"classification_tags must define exactly {sorted(REQUIRED_TAGS)}")

    policy = doc.get("policy")
    excluded: set[str] = set()
    if not isinstance(policy, dict):
        err("policy must be a mapping")
    else:
        novelty = policy.get("novelty_ledger")
        if isinstance(novelty, dict) and isinstance(novelty.get("excluded_tags"), list):
            excluded = set(novelty["excluded_tags"])
        if excluded != EXCLUDED_FROM_NOVELTY:
            err(f"policy.novelty_ledger.excluded_tags must equal {sorted(EXCLUDED_FROM_NOVELTY)}")
        if not isinstance(policy.get("source_boundary"), str) or not policy["source_boundary"]:
            err("policy.source_boundary must state the graph/phase-depth boundary")

    slices = doc.get("slices")
    if not isinstance(slices, list) or not slices:
        err("slices must be a non-empty list")
        return errors

    seen_ids: set[str] = set()
    for index, item in enumerate(slices):
        where = f"slices[{index}]"
        if not isinstance(item, dict):
            err(f"{where} must be a mapping")
            continue
        slice_id = item.get("id")
        if not isinstance(slice_id, str) or not slice_id:
            err(f"{where}.id must be a non-empty string")
        elif slice_id in seen_ids:
            err(f"{where}.id duplicates {slice_id!r}")
        else:
            seen_ids.add(slice_id)

        tag = item.get("classification")
        if tag not in REQUIRED_TAGS:
            err(f"{where}.classification is invalid: {tag!r}")
        novelty = item.get("novelty_ledger")
        if not isinstance(novelty, bool):
            err(f"{where}.novelty_ledger must be boolean")
        elif tag in EXCLUDED_FROM_NOVELTY and novelty:
            err(f"{where} uses excluded tag {tag} but novelty_ledger is true")
        elif tag == "BROCKIAN_RESULT" and not novelty:
            err(f"{where} tags a BROCKIAN_RESULT but novelty_ledger is false")

        locator = item.get("source_locator")
        if not isinstance(locator, dict) or not locator:
            err(f"{where}.source_locator must be a non-empty mapping")
        elif "pages" in locator:
            locator_pages = locator["pages"]
            if (
                not isinstance(locator_pages, list)
                or not locator_pages
                or any(not isinstance(page, int) or page <= 0 for page in locator_pages)
            ):
                err(f"{where}.source_locator.pages must be positive page numbers")
            elif page_count is not None and any(page > page_count for page in locator_pages):
                err(f"{where}.source_locator.pages exceeds source.page_count")
        elif not isinstance(locator.get("relation"), str) or not locator["relation"]:
            err(f"{where}.source_locator needs pages or a non-empty relation")

        status = item.get("implementation_status")
        if status not in VALID_STATUSES:
            err(f"{where}.implementation_status is invalid: {status!r}")
            continue
        declarations = item.get("declarations")
        if not isinstance(declarations, list) or any(not isinstance(d, str) for d in declarations):
            err(f"{where}.declarations must be a list of names")
            continue

        files = _source_files(item)
        if status in {"registry_verified", "lean_source_pending_axle"}:
            if not declarations:
                err(f"{where} status {status} requires declarations")
            if not files:
                err(f"{where} status {status} requires source_file(s)")
            for rel in files:
                if _repo_file(rel) is None:
                    err(f"{where} source file does not exist: {rel!r}")
            for declaration in declarations:
                if files and not _declaration_exists(declaration, files):
                    err(f"{where} declaration is absent from its source files: {declaration}")

        if status == "registry_verified":
            for declaration in declarations:
                register = registry.get(declaration)
                if register not in GREEN_REGISTERS:
                    err(f"{where} registry declaration is not green: {declaration} ({register})")
        elif status == "lean_source_pending_axle":
            for declaration in declarations:
                if registry.get(declaration) in GREEN_REGISTERS:
                    err(f"{where} declaration is already green; advance status explicitly: {declaration}")
        elif status == "queued" and declarations:
            err(f"{where} queued slices must not claim declarations")
        elif status == "documented_empirical":
            artifact = item.get("artifact_path")
            if _repo_file(artifact) is None:
                err(f"{where}.artifact_path must resolve to an existing file")
            if declarations:
                err(f"{where} empirical slices must not claim Lean declarations")

    return errors


def validate_path(path: Path, registry: dict[str, str] | None = None) -> list[str]:
    try:
        doc = yaml.safe_load(path.read_text(encoding="utf-8"))
    except Exception as exc:  # pragma: no cover - exercised by CLI failures
        return [f"{path}: invalid YAML: {exc}"]
    if not isinstance(doc, dict):
        return [f"{path}: manifest root must be a mapping"]
    actual_registry = registry if registry is not None else load_registry()
    return validate_document(copy.deepcopy(doc), actual_registry, str(path))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("paths", nargs="*", help="manifest paths (defaults to the repository glob)")
    args = parser.parse_args()
    paths = [Path(p) for p in args.paths]
    if not paths:
        paths = [Path(p) for p in sorted(glob.glob(str(REPO / DEFAULT_GLOB)))]
    if not paths:
        print(f"no reference-spine manifests matched {DEFAULT_GLOB}")
        return 1

    registry = load_registry()
    errors: list[str] = []
    for path in paths:
        current = validate_path(path, registry)
        errors.extend(current)
        resolved = path.resolve()
        try:
            display = resolved.relative_to(REPO)
        except ValueError:
            display = resolved
        print(f"[{'FAIL' if current else 'OK'}] {display}")
    for error in errors:
        print(f"  ERR {error}")
    if errors:
        print(f"reference-spine firewall failed with {len(errors)} error(s)")
        return 1
    print(f"reference-spine firewall clean ({len(paths)} manifest(s))")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
