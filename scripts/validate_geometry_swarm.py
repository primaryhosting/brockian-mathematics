"""Validate the Classical Geometry Swarm benchmark.

The benchmark is deliberately a source-guided task ledger, not a theorem ledger.
It may point to existing green declarations as baselines, but it cannot claim new
declarations or enter the novelty ledger. Run from the repository root:

    python3 scripts/validate_geometry_swarm.py
"""
from __future__ import annotations

import argparse
import copy
import json
import re
from pathlib import Path
from typing import Any

import yaml


REPO = Path(__file__).resolve().parents[1]
DEFAULT_PATH = REPO / "benchmarks" / "classical-geometry-swarm.yaml"
GREEN_REGISTERS = {"PROVED", "DEFINITION", "DISCHARGED"}
VALID_CLASSIFICATIONS = {
    "CLASSICAL_REFERENCE",
    "BROCKIAN_BRIDGE",
    "EMPIRICAL_COMPUTATION",
}
VALID_STATES = {"benchmark_ready", "specification_queued"}
REQUIRED_STAGES = ["explore", "formalize", "prove", "attack", "audit"]


def load_registry(path: Path = REPO / "registry" / "theorems.json") -> dict[str, str]:
    document = json.loads(path.read_text(encoding="utf-8"))
    return {item["name"]: item["register"] for item in document.get("theorems", [])}


def _file_exists(rel: str) -> bool:
    if not isinstance(rel, str):
        return False
    path = (REPO / rel).resolve()
    try:
        path.relative_to(REPO)
    except ValueError:
        return False
    return path.is_file()


def validate_document(doc: dict[str, Any], registry: dict[str, str], label: str) -> list[str]:
    errors: list[str] = []

    def err(message: str) -> None:
        errors.append(f"{label}: {message}")

    if doc.get("schema_version") != 1:
        err("schema_version must be 1")
    if not isinstance(doc.get("benchmark_id"), str) or not doc["benchmark_id"]:
        err("benchmark_id must be a non-empty string")

    policy = doc.get("source_policy")
    if not isinstance(policy, dict):
        err("source_policy must be a mapping")
    else:
        if policy.get("theorem_classification") != "classical_reference_only":
            err("source_policy.theorem_classification must be classical_reference_only")
        if policy.get("novelty_ledger") is not False:
            err("source_policy.novelty_ledger must be false")
        if policy.get("redistribution") != "metadata_only":
            err("source_policy.redistribution must be metadata_only")

    stages = doc.get("stages")
    if stages != REQUIRED_STAGES:
        err(f"stages must equal {REQUIRED_STAGES}")
    contracts = doc.get("stage_contracts")
    if not isinstance(contracts, dict) or set(contracts) != set(REQUIRED_STAGES):
        err("stage_contracts must define every required stage exactly once")
    else:
        for stage in REQUIRED_STAGES:
            contract = contracts[stage]
            if not isinstance(contract, dict) or not isinstance(contract.get("role"), str):
                err(f"stage_contracts.{stage} needs a role")
            if not isinstance(contract, dict) or not isinstance(contract.get("required_output"), str):
                err(f"stage_contracts.{stage} needs required_output")

    source_ids: set[str] = set()
    source_hashes: dict[str, str] = {}
    sources = doc.get("sources")
    if not isinstance(sources, list) or not sources:
        err("sources must be a non-empty list")
    else:
        for index, source in enumerate(sources):
            where = f"sources[{index}]"
            if not isinstance(source, dict):
                err(f"{where} must be a mapping")
                continue
            source_id = source.get("id")
            if not isinstance(source_id, str) or not source_id:
                err(f"{where}.id must be a non-empty string")
            elif source_id in source_ids:
                err(f"{where}.id duplicates {source_id!r}")
            else:
                source_ids.add(source_id)
            for field in ("title", "author", "edition_or_version", "uploaded_filename", "rights_note"):
                if not isinstance(source.get(field), str) or not source[field]:
                    err(f"{where}.{field} must be a non-empty string")
            digest = source.get("pdf_sha256")
            if not isinstance(digest, str) or re.fullmatch(r"[0-9a-f]{64}", digest) is None:
                err(f"{where}.pdf_sha256 must be a lowercase SHA-256 digest")
            elif digest in source_hashes:
                err(f"{where}.pdf_sha256 duplicates {source_hashes[digest]}")
            else:
                source_hashes[digest] = str(source_id or where)
            if not isinstance(source.get("pdf_page_count"), int) or source["pdf_page_count"] <= 0:
                err(f"{where}.pdf_page_count must be a positive integer")
            if source.get("page_numbering") != "printed_pages":
                err(f"{where}.page_numbering must be printed_pages")

    tracks = doc.get("tracks")
    if not isinstance(tracks, list) or not tracks:
        err("tracks must be a non-empty list")
        return errors

    seen_track_ids: set[str] = set()
    for index, track in enumerate(tracks):
        where = f"tracks[{index}]"
        if not isinstance(track, dict):
            err(f"{where} must be a mapping")
            continue
        track_id = track.get("id")
        if not isinstance(track_id, str) or not track_id:
            err(f"{where}.id must be a non-empty string")
        elif track_id in seen_track_ids:
            err(f"{where}.id duplicates {track_id!r}")
        else:
            seen_track_ids.add(track_id)
        if track.get("priority") not in {"P0", "P1", "P2"}:
            err(f"{where}.priority must be P0, P1, or P2")
        if track.get("classification") not in VALID_CLASSIFICATIONS:
            err(f"{where}.classification must be a non-novelty classification")
        if track.get("novelty_ledger") is not False:
            err(f"{where}.novelty_ledger must be false")
        if track.get("state") not in VALID_STATES:
            err(f"{where}.state is invalid")
        if not isinstance(track.get("target"), str) or not track["target"]:
            err(f"{where}.target must be a non-empty string")
        for field in ("required_assumptions", "adversarial_cases"):
            values = track.get(field)
            if not isinstance(values, list) or not values or any(not isinstance(v, str) or not v for v in values):
                err(f"{where}.{field} must be a non-empty list of strings")
        if track.get("proposed_declarations") != []:
            err(f"{where}.proposed_declarations must be empty until a Lean source exists")

        anchors = track.get("source_anchors")
        if not isinstance(anchors, list) or not anchors:
            err(f"{where}.source_anchors must be a non-empty list")
        else:
            for anchor_index, anchor in enumerate(anchors):
                anchor_where = f"{where}.source_anchors[{anchor_index}]"
                if not isinstance(anchor, dict):
                    err(f"{anchor_where} must be a mapping")
                    continue
                if anchor.get("source_id") not in source_ids:
                    err(f"{anchor_where}.source_id does not resolve")
                pages = anchor.get("printed_pages")
                if not isinstance(pages, list) or not pages or any(not isinstance(p, int) or p <= 0 for p in pages):
                    err(f"{anchor_where}.printed_pages must be positive integers")
                if not isinstance(anchor.get("anchor"), str) or not anchor["anchor"]:
                    err(f"{anchor_where}.anchor must be a non-empty string")

        baseline = track.get("existing_baseline")
        if baseline is not None:
            if not isinstance(baseline, dict):
                err(f"{where}.existing_baseline must be a mapping")
            else:
                files = baseline.get("source_files")
                declarations = baseline.get("declarations")
                if not isinstance(files, list) or not files or any(not _file_exists(path) for path in files):
                    err(f"{where}.existing_baseline.source_files must resolve to repository files")
                if not isinstance(declarations, list) or not declarations or any(not isinstance(d, str) for d in declarations):
                    err(f"{where}.existing_baseline.declarations must be a non-empty list of names")
                else:
                    for declaration in declarations:
                        if registry.get(declaration) not in GREEN_REGISTERS:
                            err(f"{where}.existing_baseline declaration is not green: {declaration}")

    return errors


def validate_path(path: Path, registry: dict[str, str] | None = None) -> list[str]:
    try:
        document = yaml.safe_load(path.read_text(encoding="utf-8"))
    except Exception as exc:  # pragma: no cover - CLI failure path
        return [f"{path}: invalid YAML: {exc}"]
    if not isinstance(document, dict):
        return [f"{path}: benchmark root must be a mapping"]
    actual_registry = load_registry() if registry is None else registry
    return validate_document(copy.deepcopy(document), actual_registry, str(path))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("path", nargs="?", type=Path, default=DEFAULT_PATH)
    args = parser.parse_args()
    errors = validate_path(args.path)
    for error in errors:
        print(f"ERR {error}")
    if errors:
        print(f"geometry-swarm firewall failed with {len(errors)} error(s)")
        return 1
    print(f"geometry-swarm firewall clean ({args.path})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
