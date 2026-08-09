import json
from aristotle.push_fleet_snapshot import build_snapshot, classify_domain

MANIFEST = {
    "solvers": [
        {"id": "j1", "name": "Algebra012", "status": "RUNNING",
         "account": "admin", "created": "2 days ago"},
        {"id": "j2", "name": "NTGaps2", "status": "IDLE", "account": "chris",
         "created": "2 days ago", "verdict": "PROVED",
         "finished_at": "2026-08-08T10:00:00Z"},
        {"id": "j3", "name": "Crypto2", "status": "IDLE", "account": "admin",
         "created": "3 days ago", "verdict": "STOPPED",
         "finished_at": "2026-08-07T09:00:00Z"},
        {"id": "j4", "name": "ms-cayley", "status": "IDLE", "account": "admin",
         "created": "9 days ago", "verdict": "BASELINE"},
        # pre-wiring PROVED record: finished_at present but null (the manifest
        # projects it exactly like verdict) -- must sort LAST, never crash
        {"id": "j5", "name": "Spectral7", "status": "IDLE", "account": "chris",
         "created": "20 days ago", "verdict": "PROVED", "finished_at": None},
    ]
}

def test_build_snapshot_shape():
    snap = build_snapshot(MANIFEST, now_iso="2026-08-08T12:00:00Z")
    assert snap["id"] == 1
    assert snap["generated_at"] == "2026-08-08T12:00:00Z"
    assert [j["name"] for j in snap["running"]] == ["Algebra012"]
    # newest first; BASELINE excluded; null-timestamped record last with "" sentinel
    assert [v["name"] for v in snap["recent_verdicts"]] == ["NTGaps2", "Crypto2", "Spectral7"]
    assert snap["recent_verdicts"][-1]["finished_at"] == ""
    assert snap["domain_counts"]["Algebra"] == 1

def test_baseline_verdicts_excluded():
    snap = build_snapshot(MANIFEST, now_iso="2026-08-08T12:00:00Z")
    assert all(v["verdict"] in ("PROVED", "STOPPED")
               for v in snap["recent_verdicts"])

def test_classify_domain():
    assert classify_domain("ms-cayley") == "Named theorems"
    assert classify_domain("NumberTheory03") == "Number theory"
    assert classify_domain("TotallyUnknownJob") == "Other"

def test_recent_verdicts_capped_at_20():
    jobs = [{"id": f"j{i}", "name": f"n{i}", "status": "IDLE", "account": "a",
             "created": "1 day ago", "verdict": "PROVED",
             "finished_at": f"2026-08-0{1 + i % 7}T00:00:0{i % 10}Z"}
            for i in range(30)]
    snap = build_snapshot({"solvers": jobs}, now_iso="2026-08-08T12:00:00Z")
    assert len(snap["recent_verdicts"]) == 20

def test_snapshot_size_under_50kb_at_fleet_scale():
    # real fleet is ~191 solvers; exercise the budget at 250
    jobs = [{"id": f"j{i}", "name": f"NumberTheory{i:03d}", "status": "IDLE",
             "account": "admin", "created": "1 day ago",
             "verdict": "PROVED" if i % 3 == 0 else "BASELINE",
             "finished_at": "2026-08-08T00:00:00Z"} for i in range(250)]
    snap = build_snapshot({"solvers": jobs}, now_iso="2026-08-08T12:00:00Z")
    assert len(json.dumps(snap)) < 50_000

def test_build_snapshot_empty_manifest():
    snap = build_snapshot({"solvers": []}, now_iso="2026-08-08T12:00:00Z")
    assert snap["running"] == [] and snap["recent_verdicts"] == []
