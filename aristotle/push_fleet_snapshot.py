#!/usr/bin/env python3
"""Condense solver_manifest.json into a single Supabase row for the
Riemann Lab Solver Fleet panel. Called from solver_watch.py at end of
cycle; failure is logged and NEVER fatal to the watcher."""
import datetime
import json
import os
import sys
import urllib.request
from pathlib import Path

MANIFEST_PATH = Path(__file__).resolve().parent / "solver_manifest.json"
MAX_VERDICTS = 20

# Domain is DERIVED from the job-name prefix (the manifest has no domain field).
# Transparent, deterministic, documented; the panel labels it "by area (derived
# from job names)". First match wins; unknown names land in "Other".
DOMAIN_PREFIXES = [
    ("ms-", "Named theorems"), ("qc-", "QC batches"),
    ("Algebra", "Algebra"), ("Analysis", "Analysis"), ("Topology", "Topology"),
    ("SetTheory", "Set theory"), ("Probability", "Probability"),
    ("Combinatorics", "Combinatorics"), ("Geometry", "Geometry"),
    ("NumberTheory", "Number theory"), ("NT", "Number theory"),
    ("CSLogic", "CS & logic"), ("QuantumInfo", "Quantum info"),
    ("PhysicsQM", "Physics"), ("Crypto", "Crypto"), ("InfoTheory", "Info theory"),
    ("Sieve", "Brockian frontier"), ("Spectral", "Brockian frontier"),
    ("Gilbreath", "Brockian frontier"), ("PathSpectrum", "Brockian frontier"),
    ("PentagonSpectrum", "Brockian frontier"), ("KadisonSinger", "Brockian frontier"),
    ("Sensitivity", "Brockian frontier"),
]


def classify_domain(name: str) -> str:
    for prefix, domain in DOMAIN_PREFIXES:
        if name.startswith(prefix):
            return domain
    return "Other"


def build_snapshot(manifest: dict, now_iso: str) -> dict:
    jobs = manifest.get("solvers", [])
    running = [{"name": j["name"], "account": j.get("account", ""),
                "domain": classify_domain(j["name"])}
               for j in jobs if j.get("status") == "RUNNING"]
    # Only real watch-observed outcomes; BASELINE = finished before the watch
    # existed and must not flood the recent list.
    finished = [j for j in jobs if j.get("verdict") in ("CANDIDATE", "PROVED", "STOPPED")]
    # finished_at is stamped by solver_watch at the RUNNING->IDLE transition;
    # pre-wiring records carry it as ABSENT or null -- `or ""` tolerates both
    # (None would raise TypeError under sort) and sorts them last.
    finished.sort(key=lambda j: j.get("finished_at") or "", reverse=True)
    verdicts = [{"name": j["name"], "verdict": j["verdict"],
                 "finished_at": j.get("finished_at") or "",
                 "domain": classify_domain(j["name"])}
                for j in finished[:MAX_VERDICTS]]
    counts: dict[str, int] = {}
    for j in jobs:
        d = classify_domain(j["name"])
        counts[d] = counts.get(d, 0) + 1
    return {"id": 1, "generated_at": now_iso, "running": running,
            "recent_verdicts": verdicts, "domain_counts": counts}


def push(snapshot: dict, url: str, service_key: str) -> None:
    req = urllib.request.Request(
        f"{url}/rest/v1/solver_fleet_snapshot",
        data=json.dumps(snapshot).encode(),
        headers={"apikey": service_key,
                 "Authorization": f"Bearer {service_key}",
                 "Content-Type": "application/json",
                 "Prefer": "resolution=merge-duplicates"},
        method="POST")
    urllib.request.urlopen(req, timeout=30).read()


def main() -> int:
    url = os.environ.get("RIEMANN_SUPABASE_URL", "").rstrip("/")
    key = os.environ.get("RIEMANN_SUPABASE_SERVICE_KEY", "")
    if not url or not key:
        print("push_fleet_snapshot: RIEMANN_SUPABASE_* not set; skipping", file=sys.stderr)
        return 0  # non-fatal by contract
    manifest = json.loads(MANIFEST_PATH.read_text())
    now = datetime.datetime.now(datetime.timezone.utc).isoformat()
    snapshot = build_snapshot(manifest, now)
    snapshot["updated_at"] = now  # merge-duplicates won't touch column defaults
    push(snapshot, url, key)
    print(f"push_fleet_snapshot: pushed at {now}")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as e:  # never crash the caller
        print(f"push_fleet_snapshot: FAILED (non-fatal): {e}", file=sys.stderr)
        sys.exit(0)
