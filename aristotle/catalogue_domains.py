#!/usr/bin/env python3
"""Catalogue new-domain proof candidates with explicit verification levels.

The catalogue never maps a local/AXLE compile directly to ``PROVED``.  Only V5
records from the reconciliation ledger are ``VERIFIED``; remote-only entries remain
``REMOTE_CANDIDATE`` and incomplete independent gates remain ``VERIFICATION_PENDING``.
"""
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent
REPO = ROOT.parent
QUEUES = [
    ROOT / name
    for name in (
        "domains_queue.json",
        "mined_queue.json",
        "next_100.json",
        "pca_lean_queue.json",
        "frontier_queue.json",
        "frontier2.json",
        "reattack_queue.json",
        "frontier_spectral.json",
        "frontier_betrothed_queue.json",
        "frontier_linalg.json",
        "frontier_riemann.json",
        "frontier_infinity.json",
        "frontier_fibonacci.json",
        "frontier_primes.json",
        "frontier_rh2.json",
        "frontier_wave2.json",
        "frontier_wave3.json",
        "frontier_wave4.json",
        "frontier_wave5.json",
    )
]
LEDGER = ROOT / "harvest_ledger.json"
BEST = ROOT / "best_proofs" / "manifest.json"
RECON = REPO / "pipeline/ledger/reviews/2026-08-13-aristotle-runtime-reconciliation.json"
OUT = REPO / "registry" / "domains.json"


def main():
    statements = {}
    for queue_file in QUEUES:
        if not queue_file.exists():
            continue
        data = json.loads(queue_file.read_text())
        items = data.get("queue", []) if isinstance(data, dict) else data
        for item in items:
            statements[item["target"]] = {
                "statement": item.get("statement"),
                "domain": item.get("tier"),
            }

    ledger = json.loads(LEDGER.read_text()) if LEDGER.exists() else {}
    best = json.loads(BEST.read_text()) if BEST.exists() else {}
    reconciliation = json.loads(RECON.read_text()) if RECON.exists() else {"targets": []}
    gates = {record["target"]: record for record in reconciliation.get("targets", [])}
    catalogue = json.loads(OUT.read_text()) if OUT.exists() else {}

    by_target = {}
    for project_id, meta in ledger.items():
        target = meta.get("target")
        if target and target in statements and meta.get("verdict") == "PROVED":
            by_target.setdefault(target, []).append((project_id, meta))

    for target, jobs in by_target.items():
        gate = gates.get(target)
        if gate and gate.get("verification_level") == "V5":
            register = "VERIFIED"
            verification = gate.get("verification_detail")
        elif target in best:
            register = "VERIFICATION_PENDING"
            verification = "selected source exists; full V5 gate incomplete"
        else:
            register = "REMOTE_CANDIDATE"
            verification = "Aristotle remote PROVED only; source/independent gate incomplete"
        project_id, meta = jobs[-1]
        catalogue[target] = {
            "register": register,
            "domain": statements[target]["domain"],
            "statement": statements[target]["statement"],
            "proof_file": (
                f"aristotle/best_proofs/{best[target]['artifact_file']}" if target in best else None
            ),
            "provenance": f"Harmonic/Aristotle {project_id} ({meta['account']})",
            "remote_proved_jobs": len(jobs),
            "verification": verification,
            "verification_level": gate.get("verification_level") if gate else "V1",
        }
    OUT.write_text(json.dumps(catalogue, indent=1) + "\n")
    counts = {}
    for entry in catalogue.values():
        counts[entry["register"]] = counts.get(entry["register"], 0) + 1
    print(f"catalogued {len(catalogue)} domain records -> {OUT}")
    print("by register:", counts)


if __name__ == "__main__":
    main()
