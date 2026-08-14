#!/usr/bin/env python3
"""Reconcile remote completions against exact sources and independent gates.

The output groups duplicate attempts by exact normalized source hash and normalized
theorem-signature hash.  Target labels are never used as the sole deduplication key.
"""
from __future__ import annotations

import collections
import datetime
import json
import os
import pathlib

try:
    from proof_identity import harvested_source_path, identity_metadata, target_is_represented
except ModuleNotFoundError:  # imported as a package in tests/tools
    from .proof_identity import harvested_source_path, identity_metadata, target_is_represented

ROOT = pathlib.Path(__file__).resolve().parent
REPO = ROOT.parent
PRIORITY = pathlib.Path(
    os.environ.get("RECONCILE_PRIORITY", ROOT / "priority_reconciliation_2026-08-13.json")
)
LEDGER = ROOT / "harvest_ledger.json"
MANIFEST = ROOT / "best_proofs" / "manifest.json"
VERIFY = ROOT / "harvest_100" / "verify_state.json"
AXLE = ROOT / "axle_verify.json"
AXIOMS = ROOT / "axiom_reports" / "index.json"
OUT_JSON = pathlib.Path(
    os.environ.get(
        "RECONCILE_OUT_JSON",
        REPO / "pipeline/ledger/reviews/2026-08-13-aristotle-runtime-reconciliation.json",
    )
)
OUT_MD = pathlib.Path(
    os.environ.get(
        "RECONCILE_OUT_MD",
        REPO / "pipeline/ledger/reviews/2026-08-13-aristotle-runtime-reconciliation.md",
    )
)


def load(path, default):
    return json.loads(path.read_text()) if path.exists() else default


def source_record(project_id, meta):
    path = harvested_source_path(ROOT / "harvest_100", meta["account"], project_id)
    if path is None:
        return {
            "project_id": project_id,
            "account": meta.get("account"),
            "source_available": False,
        }
    text = path.read_text(errors="ignore")
    identity = identity_metadata(text)
    return {
        "project_id": project_id,
        "account": meta.get("account"),
        "source_available": True,
        "source_file": path.name,
        **identity,
        "target_represented": target_is_represented(meta.get("target", ""), identity["declarations"]),
    }


def verification_level(target, jobs, selected, local_state, axle_state, axiom_state):
    source_available = any(job.get("source_available") for job in jobs)
    local_ok = False
    if selected:
        chosen = selected.get("chosen")
        local_ok = local_state.get(chosen, {}).get("compiles") is True or selected.get("compiles") is True
    artifact = selected.get("artifact_file") if selected else None
    axle_ok = bool(artifact and axle_state.get(artifact, {}).get("verified") is True)
    target_ok = bool(selected and selected.get("target_represented") is True)
    axiom = axiom_state.get(target, {})
    axiom_ok = axiom.get("status") == "standard_axioms_only"
    if local_ok and axle_ok and target_ok and axiom_ok:
        return "V5", "local Lean + AXLE + target match + saved standard-axiom report"
    if axle_ok and target_ok:
        return "V4", "AXLE pass and target match; local/axiom gate incomplete"
    if local_ok and target_ok:
        return "V3", "local Lean pass and target match; AXLE/axiom gate incomplete"
    if source_available:
        return "V2", "source downloaded; independent compile gate incomplete"
    if jobs:
        return "V1", "remote completion ledger only; source not downloaded in this snapshot"
    return "V0", "no matching remote completion record"


def main():
    priority = load(PRIORITY, {"targets": []})
    ledger = load(LEDGER, {})
    manifest = load(MANIFEST, {})
    local_state = load(VERIFY, {})
    axle_state = load(AXLE, {})
    axiom_state = load(AXIOMS, {})

    by_target = collections.defaultdict(list)
    for project_id, meta in ledger.items():
        if meta.get("verdict") == "PROVED" and meta.get("target"):
            by_target[meta["target"]].append(source_record(project_id, meta))

    records = []
    for curated in priority.get("targets", []):
        target = curated["target"]
        jobs = by_target.get(target, [])
        selected = manifest.get(target)
        level, level_detail = verification_level(
            target, jobs, selected, local_state, axle_state, axiom_state
        )
        normalized_hashes = sorted(
            {job["normalized_source_sha256"] for job in jobs if job.get("normalized_source_sha256")}
        )
        signature_hashes = sorted(
            {
                declaration["signature_sha256"]
                for job in jobs
                for declaration in job.get("declarations", [])
            }
        )
        records.append(
            {
                **curated,
                "remote_proved_jobs": len(jobs),
                "jobs": jobs,
                "distinct_normalized_sources": len(normalized_hashes),
                "normalized_source_sha256": normalized_hashes,
                "distinct_declaration_signatures": len(signature_hashes),
                "declaration_signature_sha256": signature_hashes,
                "selected": selected,
                "verification_level": level,
                "verification_detail": level_detail,
                "promotion_allowed": level == "V5",
                "axiom_report": axiom_state.get(target),
            }
        )

    counts = collections.Counter(record["verification_level"] for record in records)
    classifications = collections.Counter(record.get("provisional_classification") for record in records)
    output = {
        "schema_version": 1,
        "generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "policy": {
            "deduplication": "exact normalized source SHA-256 plus normalized declaration-signature SHA-256",
            "promotion": "V5 only: local pinned Lean + AXLE + expected-target match + saved axiom report",
            "remote_proved": "candidate provenance only",
        },
        "intake_snapshot": priority.get("intake_snapshot"),
        "counts": {
            "priority_targets": len(records),
            "verification_levels": dict(sorted(counts.items())),
            "provisional_classifications": dict(sorted(classifications.items())),
        },
        "targets": records,
    }
    OUT_JSON.parent.mkdir(parents=True, exist_ok=True)
    OUT_JSON.write_text(json.dumps(output, indent=2) + "\n")

    lines = [
        "# Aristotle priority reconciliation (runtime)",
        "",
        f"Generated: {output['generated_at']}",
        "",
        "Remote Aristotle `PROVED` is candidate provenance, not independent verification. "
        "Only V5 records are promotion-eligible.",
        "",
        "| Target | Intake | Provisional class | Gate | Distinct sources | Distinct signatures | Claim flag |",
        "|---|---|---|---:|---:|---:|---|",
    ]
    for record in records:
        flags = "; ".join(record.get("claim_flags", [])) or "—"
        lines.append(
            f"| `{record['target']}` | {record['intake_kind']} | "
            f"{record.get('provisional_classification', 'pending')} | {record['verification_level']} | "
            f"{record['distinct_normalized_sources']} | {record['distinct_declaration_signatures']} | {flags} |"
        )
    OUT_MD.write_text("\n".join(lines) + "\n")
    print(f"reconciled {len(records)} priority targets -> {OUT_JSON} and {OUT_MD}")
    print("verification levels:", dict(sorted(counts.items())))


if __name__ == "__main__":
    main()
