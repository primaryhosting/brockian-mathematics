#!/usr/bin/env python3
"""Mirror research/frontier_queue.json to Riemann Supabase (display only).

Exit codes: 0 synced · 2 BLOCKED (missing/401 service key) · 1 other error.
--dry-run prints the payload row count + first row and writes nothing.
"""
import json
import os
import sys
import urllib.error
import urllib.request

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
QUEUE = os.path.join(REPO, "research", "frontier_queue.json")


def rows(queue):
    return [{
        "id": e["id"], "statement": e["statement"],
        "lean_target": e["lean_target"], "source": e["source"],
        "scores": e["scores"], "rank": e["rank"], "status": e["status"],
        "assigned_engine": e.get("assigned_engine"),
        "evidence": e.get("evidence", {}), "history": e.get("history", []),
        "generated_at": queue["generated_at"],
    } for e in queue["entries"]]


def run(dry, env, queue_path=QUEUE):
    queue = json.load(open(queue_path))
    payload = rows(queue)
    if dry:
        print("dry-run: %d rows; first=%s" % (len(payload),
              json.dumps(payload[0])[:160]))
        return 0
    url = env.get("RIEMANN_SUPABASE_URL", "").rstrip("/")
    key = env.get("RIEMANN_SUPABASE_SERVICE_KEY") or env.get("RIEMANN_SUPABASE_KEY")
    if not url or not key:
        print("BLOCKED: service key — RIEMANN_SUPABASE_URL/SERVICE_KEY unset")
        return 2
    req = urllib.request.Request(
        url + "/rest/v1/atlas_frontier_queue?on_conflict=id",
        data=json.dumps(payload).encode(),
        headers={"apikey": key, "Authorization": "Bearer " + key,
                 "Content-Type": "application/json",
                 "Prefer": "resolution=merge-duplicates"},
        method="POST")
    try:
        with urllib.request.urlopen(req) as r:
            print("synced %d rows (HTTP %d)" % (len(payload), r.status))
            return 0
    except urllib.error.HTTPError as err:
        if err.code in (401, 403):
            print("BLOCKED: service key — HTTP %d from PostgREST "
                  "(mint a real service key; known blocker)" % err.code)
            return 2
        print("ERROR: HTTP %d — %s" % (err.code, err.read()[:300]))
        return 1
    except urllib.error.URLError as err:
        print("ERROR: connection failed — %s" % err.reason)
        return 1


def main():
    return run(dry="--dry-run" in sys.argv, env=dict(os.environ))


if __name__ == "__main__":
    sys.exit(main())
