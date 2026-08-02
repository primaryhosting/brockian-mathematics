#!/usr/bin/env python3
"""Driver for the Mathlib/PhysLean environment harvest (spec 2026-08-02, §3).

This does three things:

  1. Documents / invokes the off-Mini extraction (`ExtractEnv.lean`) that walks a BUILT
     Lean environment and emits one NDJSON record per declaration.
  2. Validates the NDJSON schema (fail-closed, honesty-first — see spec §2).
  3. Prints stats: counts by kind, #axiom-clean (PROVED-eligible), #nonstandard, #with-sorry.

IMPORTANT — this indexes an already-verified library; it does NOT re-prove anything. The
extractor records the axiom footprint Lean's own kernel already checked upstream, so the
downstream store can honestly set `verified_by: mathlib-kernel` and EXCLUDE non-clean decls
from the PROVED count. A record is PROVED-eligible (clean) iff:

    kind ∈ {theorem}  AND  sorryFree == True  AND  nonstandardAxioms == False

── Where the extraction runs (NOT the Mac Mini) ──────────────────────────────────────────
The Mini (16 GB) cannot build Mathlib. Run the extractor on a cache-reachable box (CI /
cloud) where the olean cache exists, then bring the NDJSON back to the Mini to ingest:

    lake exe cache get                                              # ensure oleans present
    lake env lean --run scripts/harvest/ExtractEnv.lean > mathlib.ndjson
    lake env lean --run scripts/harvest/ExtractEnv.lean Mathlib PhysLean > all.ndjson
    python3 scripts/harvest/run_extract.py mathlib.ndjson          # validate + stats (Mini)

Usage:
    run_extract.py <file.ndjson>     validate + print stats for an NDJSON dump
    run_extract.py --self-test       run the built-in synthetic self-test
    run_extract.py --run-cmd         print the exact off-Mini extraction command
    run_extract.py --print-lean      print the path to the Lean extractor
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

# --- schema ---------------------------------------------------------------------------------

REQUIRED_KEYS = {
    "name": str,
    "kind": str,
    "module": str,
    "type": str,
    "axioms": list,
    "sorryFree": bool,
    "nonstandardAxioms": bool,
}
VALID_KINDS = {"theorem", "lemma", "def", "structure", "inductive", "axiom"}
STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SORRY_AXIOM = "sorryAx"

LEAN_TOOL = Path(__file__).with_name("ExtractEnv.lean")
RUN_CMD = f"lake env lean --run {LEAN_TOOL} > mathlib.ndjson"


def validate_record(rec: dict, lineno: int) -> list[str]:
    """Return a list of schema/consistency errors for a single record (empty = valid)."""
    errs: list[str] = []
    if not isinstance(rec, dict):
        return [f"line {lineno}: not a JSON object"]

    for key, typ in REQUIRED_KEYS.items():
        if key not in rec:
            errs.append(f"line {lineno}: missing required key '{key}'")
        elif not isinstance(rec[key], typ):
            errs.append(
                f"line {lineno}: key '{key}' has type {type(rec[key]).__name__}, "
                f"expected {typ.__name__}"
            )
    if errs:
        return errs  # don't do value checks on a structurally broken record

    if rec["kind"] not in VALID_KINDS:
        errs.append(f"line {lineno}: kind '{rec['kind']}' not in {sorted(VALID_KINDS)}")
    if not all(isinstance(a, str) for a in rec["axioms"]):
        errs.append(f"line {lineno}: 'axioms' must be a list of strings")
        return errs

    axioms = set(rec["axioms"])
    # Consistency: the extractor's booleans must agree with the axiom footprint (honesty §2).
    expected_sorry_free = SORRY_AXIOM not in axioms
    if rec["sorryFree"] != expected_sorry_free:
        errs.append(
            f"line {lineno}: sorryFree={rec['sorryFree']} contradicts axioms "
            f"(sorryAx {'present' if not expected_sorry_free else 'absent'})"
        )
    expected_nonstd = any(a not in STD_AXIOMS for a in axioms)
    if rec["nonstandardAxioms"] != expected_nonstd:
        errs.append(
            f"line {lineno}: nonstandardAxioms={rec['nonstandardAxioms']} contradicts axioms "
            f"({sorted(axioms - STD_AXIOMS)})"
        )
    return errs


def is_clean_proved(rec: dict) -> bool:
    """PROVED-eligible: a theorem with a kernel-standard, sorry-free axiom footprint."""
    return (
        rec.get("kind") in ("theorem", "lemma")
        and rec.get("sorryFree") is True
        and rec.get("nonstandardAxioms") is False
    )


def load_and_validate(lines: list[str]) -> tuple[list[dict], list[str]]:
    """Parse NDJSON lines; return (records, errors)."""
    records: list[dict] = []
    errors: list[str] = []
    for i, raw in enumerate(lines, start=1):
        raw = raw.strip()
        if not raw:
            continue
        try:
            rec = json.loads(raw)
        except json.JSONDecodeError as e:
            errors.append(f"line {i}: invalid JSON: {e}")
            continue
        rec_errs = validate_record(rec, i)
        if rec_errs:
            errors.extend(rec_errs)
        else:
            records.append(rec)
    return records, errors


def print_stats(records: list[dict]) -> None:
    total = len(records)
    by_kind: dict[str, int] = {}
    clean_proved = 0
    nonstandard = 0
    with_sorry = 0
    for rec in records:
        by_kind[rec["kind"]] = by_kind.get(rec["kind"], 0) + 1
        if rec["nonstandardAxioms"]:
            nonstandard += 1
        if not rec["sorryFree"]:
            with_sorry += 1
        if is_clean_proved(rec):
            clean_proved += 1

    modules = {rec["module"] for rec in records}
    print("=" * 62)
    print(f"  Harvest NDJSON stats  ({total} valid records)")
    print("=" * 62)
    print("  by kind:")
    for kind in sorted(by_kind):
        print(f"    {kind:<12} {by_kind[kind]:>8}")
    print("-" * 62)
    print(f"  distinct modules              {len(modules):>8}")
    print(f"  axiom-clean PROVED-eligible   {clean_proved:>8}  "
          f"(theorem + sorryFree + no nonstd axioms)")
    print(f"  nonstandard-axiom decls       {nonstandard:>8}  (EXCLUDED from clean PROVED)")
    print(f"  decls containing sorry        {with_sorry:>8}")
    print("=" * 62)
    print("  NOTE: this store is verified_by=mathlib-kernel (indexed, NOT re-proved).")


# --- self-test ------------------------------------------------------------------------------

SELF_TEST_NDJSON = "\n".join([
    # clean theorem — PROVED-eligible
    json.dumps({
        "name": "Nat.add_comm", "kind": "theorem", "module": "Mathlib.Data.Nat.Basic",
        "type": "∀ (n m : ℕ), n + m = m + n",
        "axioms": ["propext", "Classical.choice", "Quot.sound"],
        "sorryFree": True, "nonstandardAxioms": False,
    }),
    # theorem with zero axioms — also clean
    json.dumps({
        "name": "Nat.zero_le", "kind": "theorem", "module": "Mathlib.Data.Nat.Basic",
        "type": "∀ (n : ℕ), 0 ≤ n", "axioms": [],
        "sorryFree": True, "nonstandardAxioms": False,
    }),
    # theorem using a nonstandard axiom — excluded from clean PROVED
    json.dumps({
        "name": "Foo.uses_lc", "kind": "theorem", "module": "Foo.Bar",
        "type": "P", "axioms": ["propext", "Foo.myAxiom"],
        "sorryFree": True, "nonstandardAxioms": True,
    }),
    # theorem with a sorry — not sorryFree, and sorryAx is nonstandard
    json.dumps({
        "name": "Foo.holey", "kind": "theorem", "module": "Foo.Bar",
        "type": "Q", "axioms": ["sorryAx"],
        "sorryFree": False, "nonstandardAxioms": True,
    }),
    # a definition
    json.dumps({
        "name": "Nat.double", "kind": "def", "module": "Foo.Defs",
        "type": "ℕ → ℕ", "axioms": [],
        "sorryFree": True, "nonstandardAxioms": False,
    }),
    # a structure
    json.dumps({
        "name": "Point", "kind": "structure", "module": "Foo.Defs",
        "type": "Type", "axioms": [],
        "sorryFree": True, "nonstandardAxioms": False,
    }),
])


def run_self_test() -> int:
    print("[self-test] parsing 6 synthetic records ...")
    records, errors = load_and_validate(SELF_TEST_NDJSON.splitlines())
    if errors:
        print("[self-test] FAIL — unexpected validation errors on good data:")
        for e in errors:
            print("   ", e)
        return 1
    assert len(records) == 6, f"expected 6 records, got {len(records)}"
    clean = sum(is_clean_proved(r) for r in records)
    assert clean == 2, f"expected 2 clean PROVED-eligible, got {clean}"
    print("[self-test] OK — 6 records parsed, 2 clean PROVED-eligible as expected.\n")
    print_stats(records)

    # negative test: a record whose booleans lie about its axioms must be rejected.
    print("\n[self-test] negative case — record with inconsistent booleans:")
    bad = json.dumps({
        "name": "Bad.liar", "kind": "theorem", "module": "X",
        "type": "T", "axioms": ["sorryAx"],
        "sorryFree": True, "nonstandardAxioms": False,  # both lies
    })
    _, bad_errs = load_and_validate([bad])
    if len(bad_errs) < 2:
        print("[self-test] FAIL — inconsistent record was not fully rejected:", bad_errs)
        return 1
    for e in bad_errs:
        print("    caught:", e)
    print("\n[self-test] PASSED.")
    return 0


# --- main -----------------------------------------------------------------------------------

def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument("ndjson", nargs="?", help="path to an NDJSON dump to validate")
    parser.add_argument("--self-test", action="store_true", help="run the built-in self-test")
    parser.add_argument("--run-cmd", action="store_true",
                        help="print the off-Mini extraction command and exit")
    parser.add_argument("--print-lean", action="store_true",
                        help="print the path to the Lean extractor and exit")
    args = parser.parse_args(argv)

    if args.run_cmd:
        print(RUN_CMD)
        return 0
    if args.print_lean:
        print(LEAN_TOOL)
        return 0
    if args.self_test or not args.ndjson:
        return run_self_test()

    path = Path(args.ndjson)
    if not path.exists():
        print(f"error: {path} not found", file=sys.stderr)
        return 2
    lines = path.read_text(encoding="utf-8").splitlines()
    records, errors = load_and_validate(lines)
    if errors:
        print(f"VALIDATION FAILED — {len(errors)} error(s):", file=sys.stderr)
        for e in errors[:50]:
            print("   ", e, file=sys.stderr)
        if len(errors) > 50:
            print(f"    ... and {len(errors) - 50} more", file=sys.stderr)
        # still print stats for the records that DID validate, then fail-close.
        if records:
            print()
            print_stats(records)
        return 1
    print_stats(records)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
