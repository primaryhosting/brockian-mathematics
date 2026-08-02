"""Ingest a Mathlib / PhysLean / Brockian NDJSON dump into the verified_declarations
SQLite store (harvest spec §4/§5).

The extractor (a Lean env-walker, spec §3) emits one JSON object per line:

    {"name": "...", "kind": "theorem", "module": "Mathlib.Foo.Bar",
     "type": "...", "axioms": ["propext", ...], "sorryFree": true}

plus, per-dump, a `source` (brockian|mathlib|physlean) and `source_rev` (upstream
revision). Records may carry their own `source`/`source_rev`; otherwise the --source /
--source-rev flags supply the defaults.

This module:
  * derives `register` by REUSING gen_registry.derive_register semantics (spec §5) —
    theorem/lemma + axiom-clean + sorry-free → PROVED; def/structure → DEFINITION;
    extra axioms → PROVED tagged `nonstandard_axioms` (excluded from the clean headline);
  * sets `verified_by` from the source (AXLE / mathlib-kernel / physlean-kernel);
  * DE-DUPES against Brockian-original: a name declared in a `Brockian.*` module is
    source=brockian and WINS over any mathlib/physlean duplicate of the same name;
  * is IDEMPOTENT — keyed on (name, source_rev); re-ingesting an unchanged dump is a no-op;
  * prints a split-by-source summary and an honest, source-split honesty_report().

HONESTY (spec §2, load-bearing): counts are ALWAYS split by source. honesty_report()
refuses to emit a merged "N proved" that mixes source=brockian (we verified via AXLE)
with source=mathlib (we indexed a kernel-verified library) — it raises if asked to merge.
nonstandard-axiom decls are excluded from the clean PROVED headline.

Pure stdlib. `python3 scripts/harvest/ingest.py --selftest` runs on synthetic data.
"""
from __future__ import annotations

import argparse
import json
import os
import sqlite3
import sys
from datetime import datetime, timezone

# ── reuse the register-derivation semantics from gen_registry (spec §5) ──────────
_SCRIPTS = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _SCRIPTS not in sys.path:
    sys.path.insert(0, _SCRIPTS)
from gen_registry import ALLOWED_AXIOMS, DeclFacts, Flags, derive_register  # noqa: E402

DEFAULT_DB = os.path.join(os.path.dirname(os.path.abspath(__file__)), "verified.db")
SCHEMA_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "schema.sql")

# provenance facet: how a source earns its register (spec §2)
VERIFIED_BY = {
    "brockian": "AXLE",             # our independent gate
    "mathlib": "mathlib-kernel",    # kernel-verified upstream, indexed by us
    "physlean": "physlean-kernel",
}
# kinds that are DEFINITIONS, not claims (spec §5: def/structure → DEFINITION)
_DEFINITION_KINDS = {"def", "abbrev", "definition", "structure", "inductive", "class", "instance"}


# ── register derivation ─────────────────────────────────────────────────────────

def derive_harvest_register(kind: str, axioms: list[str], sorry_free: bool) -> tuple[str, bool]:
    """Return (register, nonstandard_axioms) for a harvested decl.

    Reuses gen_registry.derive_register: theorem/lemma that is sorry-free and
    axiom-clean → PROVED; def/structure → DEFINITION; a sorry-free theorem whose
    ONLY deviation is nonstandard axioms → PROVED but tagged nonstandard (kept out of
    the clean headline, spec §5); anything with a sorry → UNVERIFIED.

    For harvested (mathlib/physlean) decls, kernel-verification stands in for the AXLE
    verdict that derive_register requires — the `verified_by` facet records that it was
    the Lean kernel upstream, not our AXLE gate. This keeps the register vocabulary
    identical across sources while the honesty split lives in verified_by + the report.
    """
    k = kind.lower()
    norm = "def" if k in _DEFINITION_KINDS else k  # def/structure/... → DEFINITION path
    ax = list(axioms or [])
    facts = DeclFacts(
        name="_", kind=norm, axioms=ax,
        flags=Flags(sorry=not sorry_free),
        axle_verified=True,  # kernel/AXLE attestation stands here; provenance is in verified_by
    )
    reg = derive_register(facts)
    nonstandard = not set(ax).issubset(ALLOWED_AXIOMS)
    # a sorry-free theorem/lemma that only fails the axiom-clean leg is PROVED (nonstandard-tagged)
    if reg == "UNVERIFIED" and norm in ("theorem", "lemma") and sorry_free:
        return "PROVED", True
    if reg == "PROVED":
        return "PROVED", False  # clean by construction
    return reg, nonstandard


def _canonical_source(module: str, declared: str | None, default: str) -> str:
    """Brockian-original wins: anything in a `Brockian.*` module is source=brockian."""
    if module.startswith("Brockian.") or module == "Brockian":
        return "brockian"
    return declared or default


# ── store ────────────────────────────────────────────────────────────────────────

def open_store(db_path: str) -> sqlite3.Connection:
    conn = sqlite3.connect(db_path)
    conn.row_factory = sqlite3.Row
    with open(SCHEMA_PATH) as f:
        conn.executescript(f.read())
    conn.commit()
    return conn


def _row_payload(rec: dict, default_source: str, default_rev: str) -> dict:
    """Normalize one NDJSON record into a store row (register derived, source canonicalized)."""
    name = rec["name"]
    module = rec.get("module", "")
    source = _canonical_source(module, rec.get("source"), default_source)
    kind = rec.get("kind", "theorem")
    axioms = rec.get("axioms") or []
    sorry_free = bool(rec.get("sorryFree", rec.get("sorry_free", True)))
    register, nonstandard = derive_harvest_register(kind, axioms, sorry_free)
    return {
        "name": name,
        "source": source,
        "module": module,
        "kind": kind,
        "register": register,
        "verified_by": VERIFIED_BY[source],
        "axioms": json.dumps(sorted(axioms)),
        "sorry_free": 1 if sorry_free else 0,
        "nonstandard_axioms": 1 if nonstandard else 0,
        "type": rec.get("type", ""),
        "source_rev": rec.get("source_rev", default_rev),
    }


_COMPARE_COLS = ("source", "module", "kind", "register", "verified_by",
                 "axioms", "sorry_free", "nonstandard_axioms", "type", "source_rev")


def ingest_records(conn: sqlite3.Connection, records, default_source: str = "mathlib",
                   default_rev: str = "") -> dict:
    """Upsert records with Brockian-original dedup + idempotency. Returns counts."""
    counts = {"inserted": 0, "updated": 0, "unchanged": 0, "deduped": 0}
    now = datetime.now(timezone.utc).isoformat()
    cur = conn.cursor()
    for rec in records:
        row = _row_payload(rec, default_source, default_rev)
        existing = cur.execute(
            "SELECT * FROM verified_declarations WHERE name = ?", (row["name"],)
        ).fetchone()
        if existing is not None:
            # Brockian-original wins: never let a mathlib/physlean dup overwrite a brockian row.
            if existing["source"] == "brockian" and row["source"] != "brockian":
                counts["deduped"] += 1
                continue
            same = all(existing[c] == row[c] for c in _COMPARE_COLS)
            if same:
                counts["unchanged"] += 1  # idempotent: keep original harvested_at
                continue
            cur.execute(
                "UPDATE verified_declarations SET source=?, module=?, kind=?, register=?, "
                "verified_by=?, axioms=?, sorry_free=?, nonstandard_axioms=?, type=?, "
                "harvested_at=?, source_rev=? WHERE name=?",
                (row["source"], row["module"], row["kind"], row["register"], row["verified_by"],
                 row["axioms"], row["sorry_free"], row["nonstandard_axioms"], row["type"],
                 now, row["source_rev"], row["name"]),
            )
            counts["updated"] += 1
        else:
            cur.execute(
                "INSERT INTO verified_declarations (name, source, module, kind, register, "
                "verified_by, axioms, sorry_free, nonstandard_axioms, type, harvested_at, "
                "source_rev) VALUES (?,?,?,?,?,?,?,?,?,?,?,?)",
                (row["name"], row["source"], row["module"], row["kind"], row["register"],
                 row["verified_by"], row["axioms"], row["sorry_free"], row["nonstandard_axioms"],
                 row["type"], now, row["source_rev"]),
            )
            counts["inserted"] += 1
    conn.commit()
    return counts


def _iter_ndjson(path: str):
    with open(path) as f:
        for line in f:
            line = line.strip()
            if line:
                yield json.loads(line)


# ── honest reporting (spec §2 — always split by source; NEVER merge) ──────────────

def source_split(conn: sqlite3.Connection) -> dict:
    """register × source counts, plus clean-PROVED per source (nonstandard excluded)."""
    out: dict = {"by_source_register": {}, "clean_proved": {}, "nonstandard_proved": {}}
    for r in conn.execute(
        "SELECT source, register, nonstandard_axioms, COUNT(*) n "
        "FROM verified_declarations GROUP BY source, register, nonstandard_axioms"
    ):
        out["by_source_register"].setdefault(r["source"], {})
        key = r["register"] + ("(nonstandard)" if r["nonstandard_axioms"] else "")
        out["by_source_register"][r["source"]][key] = (
            out["by_source_register"][r["source"]].get(key, 0) + r["n"])
        if r["register"] == "PROVED":
            bucket = "nonstandard_proved" if r["nonstandard_axioms"] else "clean_proved"
            out[bucket][r["source"]] = out[bucket].get(r["source"], 0) + r["n"]
    return out


def honesty_report(conn: sqlite3.Connection, merge: bool = False) -> dict:
    """Print (and return) the source-split honest headline.

    HONESTY GUARD (spec §2): `merge=True` asks for a single blended "N proved" that would
    conflate AXLE-verified Brockian work with kernel-indexed Mathlib. That is exactly the
    overclaim this store exists to prevent — so it RAISES rather than emit such a number.
    """
    if merge:
        raise RuntimeError(
            "honesty violation: refusing to merge PROVED counts across sources. "
            "Brockian (verified_by=AXLE) and mathlib/physlean (verified_by=*-kernel) are "
            "indexed-vs-proved by construction and must be reported split by source (spec §2)."
        )
    split = source_split(conn)
    clean = split["clean_proved"]
    nonstd = split["nonstandard_proved"]
    parts = [f"{src}={clean[src]} ({VERIFIED_BY[src]})" for src in sorted(clean)]
    print("PROVED (clean, axioms ⊆ {propext, Classical.choice, Quot.sound}):")
    print("  " + (" | ".join(parts) if parts else "(none)"))
    if nonstd:
        np = [f"{src}={nonstd[src]}" for src in sorted(nonstd)]
        print("PROVED (nonstandard-axioms, EXCLUDED from clean headline): " + " | ".join(np))
    print("Full register × source breakdown:")
    for src in sorted(split["by_source_register"]):
        regs = split["by_source_register"][src]
        detail = ", ".join(f"{k}={v}" for k, v in sorted(regs.items()))
        print(f"  {src} ({VERIFIED_BY[src]}): {detail}")
    return split


def print_summary(conn: sqlite3.Connection, counts: dict) -> None:
    total = conn.execute("SELECT COUNT(*) FROM verified_declarations").fetchone()[0]
    print(f"ingest: inserted={counts['inserted']} updated={counts['updated']} "
          f"unchanged={counts['unchanged']} deduped(brockian-wins)={counts['deduped']} "
          f"| store total={total}")
    print("split by source:")
    for r in conn.execute(
        "SELECT source, COUNT(*) n FROM verified_declarations GROUP BY source ORDER BY source"
    ):
        print(f"  {r['source']} ({VERIFIED_BY[r['source']]}): {r['n']}")


# ── synthetic self-test ───────────────────────────────────────────────────────────

_SYNTHETIC = [
    # Brockian-original, clean → PROVED / AXLE
    {"name": "Brockian.Pentagon.law", "kind": "theorem", "module": "Brockian.Pentagon",
     "type": "…", "axioms": ["propext", "Classical.choice"], "sorryFree": True,
     "source": "brockian", "source_rev": "brock-rev-1"},
    # Mathlib clean theorem → PROVED / mathlib-kernel
    {"name": "Nat.add_comm", "kind": "theorem", "module": "Mathlib.Algebra.Group.Nat",
     "type": "∀ a b, a + b = b + a", "axioms": ["propext", "Quot.sound"], "sorryFree": True},
    # Mathlib nonstandard-axiom theorem → PROVED (nonstandard, excluded from clean headline)
    {"name": "Mathlib.SomeCompute.result", "kind": "theorem", "module": "Mathlib.Compute",
     "type": "…", "axioms": ["propext", "Lean.ofReduceBool"], "sorryFree": True},
    # Mathlib def → DEFINITION
    {"name": "Finset.card", "kind": "def", "module": "Mathlib.Data.Finset.Card",
     "type": "Finset α → ℕ", "axioms": [], "sorryFree": True},
    # Mathlib structure → DEFINITION
    {"name": "Mathlib.Topology.OpenCover", "kind": "structure", "module": "Mathlib.Topology.Basic",
     "type": "…", "axioms": [], "sorryFree": True},
    # Mathlib theorem carrying a sorry → UNVERIFIED (must never read as proved)
    {"name": "Mathlib.WIP.stub", "kind": "theorem", "module": "Mathlib.WIP",
     "type": "…", "axioms": ["propext"], "sorryFree": False},
    # PhysLean clean theorem → PROVED / physlean-kernel
    {"name": "PhysLean.QM.hilbert_complete", "kind": "theorem", "module": "PhysLean.QuantumMechanics",
     "type": "…", "axioms": ["propext", "Classical.choice", "Quot.sound"], "sorryFree": True},
    # DUPLICATE NAME across sources: a name also declared Brockian-original — brockian must win.
    {"name": "Brockian.Shared.dedup_me", "kind": "theorem", "module": "Mathlib.Dup",
     "type": "mathlib copy", "axioms": ["propext"], "sorryFree": True, "source": "mathlib"},
    {"name": "Brockian.Shared.dedup_me", "kind": "theorem", "module": "Brockian.Shared",
     "type": "brockian original", "axioms": ["propext"], "sorryFree": True, "source": "brockian"},
]


def selftest() -> int:
    import tempfile
    tmp = tempfile.mkdtemp(prefix="verified-ingest-")
    db = os.path.join(tmp, "verified.db")
    conn = open_store(db)

    print("== schema load ==")
    cols = [r[1] for r in conn.execute("PRAGMA table_info(verified_declarations)")]
    print("columns:", ", ".join(cols))

    print("\n== first ingest (mathlib default) ==")
    c1 = ingest_records(conn, _SYNTHETIC, default_source="mathlib", default_rev="mathlib-rev-A")
    print_summary(conn, c1)

    print("\n== honesty_report (split by source) ==")
    honesty_report(conn)

    print("\n== idempotency: re-ingest identical dump ==")
    c2 = ingest_records(conn, _SYNTHETIC, default_source="mathlib", default_rev="mathlib-rev-A")
    print_summary(conn, c2)
    assert c2["inserted"] == 0 and c2["updated"] == 0, "re-ingest must be a no-op"
    assert c2["unchanged"] > 0, "re-ingest must count unchanged rows"

    print("\n== dedup: Brockian-original wins over the mathlib duplicate ==")
    row = conn.execute(
        "SELECT source, verified_by, type FROM verified_declarations WHERE name=?",
        ("Brockian.Shared.dedup_me",)).fetchone()
    print(f"  Brockian.Shared.dedup_me -> source={row['source']} verified_by={row['verified_by']} "
          f"type={row['type']!r}")
    assert row["source"] == "brockian", "brockian must win the dedup (regardless of ingest order)"
    # Now that the brockian row exists, a fresh mathlib duplicate must be SKIPPED (deduped),
    # never overwriting the brockian-original.
    mathlib_dup = [r for r in _SYNTHETIC
                   if r["name"] == "Brockian.Shared.dedup_me" and r.get("source") == "mathlib"]
    c_dup = ingest_records(conn, mathlib_dup, default_source="mathlib", default_rev="mathlib-rev-A")
    print(f"  re-submitting the mathlib duplicate -> deduped={c_dup['deduped']}")
    assert c_dup["deduped"] == 1, "a mathlib dup of an existing brockian row must be deduped"
    row2 = conn.execute(
        "SELECT source, type FROM verified_declarations WHERE name=?",
        ("Brockian.Shared.dedup_me",)).fetchone()
    assert row2["source"] == "brockian" and row2["type"] == "brockian original", \
        "brockian-original must remain untouched after a mathlib dup arrives"

    print("\n== register derivation spot-checks ==")
    checks = {
        "Nat.add_comm": ("PROVED", 0),
        "Mathlib.SomeCompute.result": ("PROVED", 1),   # nonstandard-tagged
        "Finset.card": ("DEFINITION", 0),
        "Mathlib.Topology.OpenCover": ("DEFINITION", 0),
        "Mathlib.WIP.stub": ("UNVERIFIED", 0),
        "PhysLean.QM.hilbert_complete": ("PROVED", 0),
    }
    for name, (want_reg, want_ns) in checks.items():
        r = conn.execute(
            "SELECT register, nonstandard_axioms FROM verified_declarations WHERE name=?",
            (name,)).fetchone()
        got = (r["register"], r["nonstandard_axioms"])
        ok = got == (want_reg, want_ns)
        print(f"  {name}: {got}  {'OK' if ok else 'FAIL expected ' + str((want_reg, want_ns))}")
        assert ok, f"{name}: register derivation mismatch"

    print("\n== honesty guard: refusing to merge sources ==")
    try:
        honesty_report(conn, merge=True)
        print("  FAIL: merge did not raise")
        return 1
    except RuntimeError as e:
        print(f"  OK: raised -> {str(e).splitlines()[0]}")

    print("\nSELFTEST PASSED")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description="Ingest NDJSON harvest dump into verified_declarations")
    ap.add_argument("ndjson", nargs="*", help="NDJSON dump file(s) from the extractor")
    ap.add_argument("--db", default=DEFAULT_DB, help=f"SQLite store path (default {DEFAULT_DB})")
    ap.add_argument("--source", default="mathlib", choices=["brockian", "mathlib", "physlean"],
                    help="default source for records lacking one")
    ap.add_argument("--source-rev", default="", help="default upstream revision (idempotency key)")
    ap.add_argument("--report", action="store_true", help="print honesty_report and exit")
    ap.add_argument("--selftest", action="store_true", help="run synthetic self-test")
    args = ap.parse_args()

    if args.selftest:
        return selftest()

    conn = open_store(args.db)
    if args.report and not args.ndjson:
        honesty_report(conn)
        return 0
    total_counts = {"inserted": 0, "updated": 0, "unchanged": 0, "deduped": 0}
    for path in args.ndjson:
        c = ingest_records(conn, _iter_ndjson(path), args.source, args.source_rev)
        for k in total_counts:
            total_counts[k] += c[k]
    print_summary(conn, total_counts)
    print()
    honesty_report(conn)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
