"""Tiny read-only HTTP API over the verified_declarations SQLite store (harvest spec §4/§6).

Serves the binding surface for the site's `<VerifiedClaim>` component (spec § A): a visual
or computational claim resolves against this API and renders each result's HONEST provenance
badge — `source` (who authored the math) + `verified_by` (how it earned its register).

Endpoints (GET only, JSON out):
  /api/verified/search?q=&source=&register=&limit=   fuzzy search over name/module/type
  /api/verified/get?name=                            exact fetch of one declaration

HONESTY (spec §2): every record returned carries BOTH `source` and `verified_by`, so the
component can NEVER render a Mathlib-indexed fact as "proved by us". This API deliberately
has no endpoint that emits a single merged PROVED count across sources.

Pure stdlib (http.server) — no new deps. `--selftest` spins the server on an ephemeral port,
queries it over real HTTP against a synthetic store, and prints the results.
"""
from __future__ import annotations

import argparse
import json
import os
import sqlite3
import sys
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

DEFAULT_DB = os.path.join(os.path.dirname(os.path.abspath(__file__)), "verified.db")
MAX_LIMIT = 500
DEFAULT_LIMIT = 50


def _connect(db_path: str) -> sqlite3.Connection:
    conn = sqlite3.connect(db_path, check_same_thread=False)
    conn.row_factory = sqlite3.Row
    return conn


def _record(row: sqlite3.Row) -> dict:
    """Shape a store row into the JSON contract for <VerifiedClaim> (provenance always present)."""
    return {
        "name": row["name"],
        "source": row["source"],
        "module": row["module"],
        "kind": row["kind"],
        "register": row["register"],
        "verified_by": row["verified_by"],
        "axioms": json.loads(row["axioms"] or "[]"),
        "sorry_free": bool(row["sorry_free"]),
        "nonstandard_axioms": bool(row["nonstandard_axioms"]),
        "type": row["type"],
        "harvested_at": row["harvested_at"],
        "source_rev": row["source_rev"],
    }


def search(conn: sqlite3.Connection, q: str = "", source: str = "", register: str = "",
           limit: int = DEFAULT_LIMIT) -> list[dict]:
    """Filtered search. `q` matches name/module/type (LIKE); source/register are exact filters."""
    limit = max(1, min(int(limit or DEFAULT_LIMIT), MAX_LIMIT))
    where, params = [], []
    if q:
        where.append("(name LIKE ? OR module LIKE ? OR type LIKE ?)")
        like = f"%{q}%"
        params += [like, like, like]
    if source:
        where.append("source = ?")
        params.append(source)
    if register:
        where.append("register = ?")
        params.append(register)
    sql = "SELECT * FROM verified_declarations"
    if where:
        sql += " WHERE " + " AND ".join(where)
    # PROVED first, then name — stable, useful default ordering for the binding UI
    sql += " ORDER BY (register='PROVED') DESC, name ASC LIMIT ?"
    params.append(limit)
    return [_record(r) for r in conn.execute(sql, params)]


def get(conn: sqlite3.Connection, name: str) -> dict | None:
    row = conn.execute(
        "SELECT * FROM verified_declarations WHERE name = ?", (name,)).fetchone()
    return _record(row) if row else None


def make_handler(conn: sqlite3.Connection):
    class Handler(BaseHTTPRequestHandler):
        def _json(self, code: int, payload) -> None:
            body = json.dumps(payload).encode()
            self.send_response(code)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Access-Control-Allow-Origin", "*")  # read-only, safe for viz binding
            self.end_headers()
            self.wfile.write(body)

        def do_GET(self):  # noqa: N802
            u = urlparse(self.path)
            qs = parse_qs(u.query)
            one = lambda k, d="": qs.get(k, [d])[0]  # noqa: E731
            if u.path == "/api/verified/search":
                results = search(conn, q=one("q"), source=one("source"),
                                 register=one("register"), limit=one("limit", str(DEFAULT_LIMIT)))
                self._json(200, {"count": len(results), "results": results})
            elif u.path == "/api/verified/get":
                name = one("name")
                if not name:
                    self._json(400, {"error": "name is required"})
                    return
                rec = get(conn, name)
                self._json(200 if rec else 404,
                           rec if rec else {"error": "not found", "name": name})
            elif u.path in ("/", "/health"):
                total = conn.execute("SELECT COUNT(*) FROM verified_declarations").fetchone()[0]
                self._json(200, {"ok": True, "store_total": total,
                                 "endpoints": ["/api/verified/search", "/api/verified/get"]})
            else:
                self._json(404, {"error": "unknown endpoint", "path": u.path})

        def log_message(self, *a):  # silence default stderr logging
            pass

    return Handler


def serve(db_path: str, host: str, port: int) -> None:
    conn = _connect(db_path)
    httpd = ThreadingHTTPServer((host, port), make_handler(conn))
    print(f"verified search API on http://{host}:{httpd.server_address[1]}  (db={db_path})")
    httpd.serve_forever()


def selftest() -> int:
    import tempfile
    import threading
    import urllib.request

    # Build a synthetic store by driving ingest.py (keeps derivation/dedup identical).
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import ingest  # noqa: E402

    tmp = tempfile.mkdtemp(prefix="verified-api-")
    db = os.path.join(tmp, "verified.db")
    conn = ingest.open_store(db)
    ingest.ingest_records(conn, ingest._SYNTHETIC, default_source="mathlib",
                          default_rev="mathlib-rev-A")
    conn.close()

    httpd = ThreadingHTTPServer(("127.0.0.1", 0), make_handler(_connect(db)))
    port = httpd.server_address[1]
    t = threading.Thread(target=httpd.serve_forever, daemon=True)
    t.start()
    base = f"http://127.0.0.1:{port}"

    def fetch(path: str):
        with urllib.request.urlopen(base + path, timeout=5) as r:
            return r.status, json.loads(r.read())

    try:
        print(f"== API up on {base} ==")

        print("\n== GET /api/verified/search?q=add (sample query) ==")
        st, body = fetch("/api/verified/search?q=add")
        print(f"  status={st} count={body['count']}")
        for rec in body["results"]:
            print(f"    {rec['name']}  [{rec['source']}/{rec['verified_by']}]  {rec['register']}")
        assert st == 200 and body["count"] >= 1

        print("\n== GET /api/verified/search?source=mathlib&register=PROVED ==")
        st, body = fetch("/api/verified/search?source=mathlib&register=PROVED")
        print(f"  status={st} count={body['count']}")
        for rec in body["results"]:
            ns = " (nonstandard)" if rec["nonstandard_axioms"] else ""
            print(f"    {rec['name']}  {rec['register']}{ns}")
        assert all(r["source"] == "mathlib" and r["register"] == "PROVED" for r in body["results"])
        # provenance is ALWAYS present — the honesty contract for <VerifiedClaim>
        assert all("source" in r and "verified_by" in r for r in body["results"])

        print("\n== GET /api/verified/get?name=Nat.add_comm ==")
        st, body = fetch("/api/verified/get?name=Nat.add_comm")
        print(f"  status={st} -> {body['name']} source={body['source']} "
              f"verified_by={body['verified_by']} register={body['register']}")
        assert st == 200 and body["verified_by"] == "mathlib-kernel"

        print("\n== dedup surfaced via API: Brockian-original wins ==")
        st, body = fetch("/api/verified/get?name=Brockian.Shared.dedup_me")
        print(f"  status={st} -> source={body['source']} verified_by={body['verified_by']}")
        assert body["source"] == "brockian" and body["verified_by"] == "AXLE"

        print("\n== GET /api/verified/get?name=Nonexistent (404) ==")
        try:
            fetch("/api/verified/get?name=Nonexistent.decl")
            print("  FAIL: expected 404")
            return 1
        except urllib.error.HTTPError as e:
            print(f"  OK: status={e.code}")
            assert e.code == 404

        print("\nSELFTEST PASSED")
        return 0
    finally:
        httpd.shutdown()


def main() -> int:
    ap = argparse.ArgumentParser(description="Read-only search API over verified_declarations")
    ap.add_argument("--db", default=DEFAULT_DB, help=f"SQLite store path (default {DEFAULT_DB})")
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, default=18831)
    ap.add_argument("--selftest", action="store_true", help="run synthetic self-test over HTTP")
    args = ap.parse_args()
    if args.selftest:
        return selftest()
    serve(args.db, args.host, args.port)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
