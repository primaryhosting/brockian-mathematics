#!/usr/bin/env python3
"""Export a SANITIZED public verified-registry from the internal source of truth.

The internal ``registry/theorems.json`` carries fields that must never be
published: ledger run identifiers, free-text provenance notes, quarantine
internals, and internal file paths. This exporter reads that file and emits a
public JSON (``torus/public/verified-registry.json``) built from an explicit
ALLOWLIST -- only known-safe fields are copied, everything else is dropped by
default. That is the honesty firewall: the public surface can only show what we
are willing to stand behind, and a field can never leak just because someone
forgot to add it to a denylist.

Honesty rules enforced here:
  * Allowlist, not denylist -- unknown fields are dropped, not published.
  * ``source`` is a provenance facet (brockian / mathlib / physlean), derived
    from the module name; the internal ``source.file`` PATH is stripped.
  * ``verified_by`` records the checker (AXLE) -- never merged with "we proved".
  * Counts are always reported SPLIT BY SOURCE so a headline can never silently
    mix "we proved" with "we indexed".

Stdlib only. Run:  python3 scripts/export_public_registry.py
"""

from __future__ import annotations

import json
import os
import sys
from collections import Counter, defaultdict

# --- Paths (repo-relative; no absolute paths baked in) ----------------------
_HERE = os.path.dirname(os.path.abspath(__file__))
_REPO = os.path.dirname(_HERE)
IN_PATH = os.path.join(_REPO, "registry", "theorems.json")
OUT_DIR = os.path.join(_REPO, "torus", "public")
OUT_PATH = os.path.join(OUT_DIR, "verified-registry.json")

# Statement text is truncated on the public surface (defensive; also keeps the
# file small). Full statements live only in the internal registry / Lean source.
STATEMENT_MAX = 280

# Registers that are allowed to render a "verified certificate" badge. CONJECTURE
# is public but must render as an explicitly UNPROVEN / claimed state, never a
# verified badge -- the component enforces that; we still export the register so
# the component can distinguish it honestly.
KNOWN_REGISTERS = {"PROVED", "DEFINITION", "CONDITIONAL", "DISCHARGED", "CONJECTURE"}

# --- Field policy -----------------------------------------------------------
# Explicit ALLOWLIST of internal top-level fields that map into public output.
# Anything not named here is STRIPPED by default.
ALLOWED_INTERNAL_FIELDS = {
    "name",
    "module",
    "register",
    "kind",
    "statement",       # truncated
    "conditional_rung",
    "discharged_by",
    "axioms",
    "verification",    # only .axle.verdict / .axle.environment / .axioms_ok extracted
    "source",          # only the provenance FACET kept; the .file PATH is stripped
    "flags",           # only .sorry -> derived sorry_free; raw flags NOT published
}

# Internal fields that are explicitly and deliberately stripped (reported).
STRIPPED_INTERNAL_FIELDS = {
    "ledger_run",       # internal ledger run ids / free text
    "provenance_note",  # internal free-text notes
    "quarantine",       # quarantine internals
}


def derive_source(module: str) -> str:
    """Provenance facet from the module namespace (spec 2)."""
    m = (module or "")
    if m.startswith("Brockian"):
        return "brockian"
    if m.startswith("PhysLean"):
        return "physlean"
    if m.startswith("Mathlib"):
        return "mathlib"
    return "unknown"


def truncate(text: str, limit: int = STATEMENT_MAX) -> str:
    text = text or ""
    if len(text) <= limit:
        return text
    return text[: limit - 1].rstrip() + "…"


def sanitize(entry: dict) -> dict:
    """Build ONE public record from ALLOWLISTED fields only."""
    module = entry.get("module") or ""
    verification = entry.get("verification") or {}
    axle = verification.get("axle") or {}
    flags = entry.get("flags") or {}

    register = entry.get("register")
    axle_verdict = axle.get("verdict")
    source = derive_source(module)

    # verified_by = the checker that produced the verdict. Only "AXLE" when AXLE
    # actually returned a verdict; never asserted for unverified/other sources.
    if source == "brockian" and axle_verdict:
        verified_by = "AXLE"
    else:
        verified_by = None

    return {
        "name": entry.get("name"),
        "module": module,
        "register": register,
        "kind": entry.get("kind"),
        "statement": truncate(entry.get("statement", "")),
        "conditional_rung": entry.get("conditional_rung"),
        "discharged_by": entry.get("discharged_by"),
        "axioms": list(entry.get("axioms") or []),
        "axioms_ok": bool(verification.get("axioms_ok", False)),
        "axle_verdict": axle_verdict,          # e.g. "verified"
        "env": axle.get("environment"),        # e.g. "lean-4.32.0"
        "sorry_free": not bool(flags.get("sorry", False)),
        "source": source,                      # provenance facet
        "verified_by": verified_by,            # checker (AXLE) or null
    }


def main() -> int:
    if not os.path.exists(IN_PATH):
        print(f"ERROR: source registry not found: {IN_PATH}", file=sys.stderr)
        return 1

    with open(IN_PATH, "r", encoding="utf-8") as fh:
        data = json.load(fh)

    theorems = data.get("theorems", [])
    if not isinstance(theorems, list):
        print("ERROR: registry 'theorems' is not a list", file=sys.stderr)
        return 1

    # Discover the full set of internal fields present (for the kept/stripped report).
    all_input_fields = set()
    for t in theorems:
        all_input_fields.update(t.keys())

    public_records = [sanitize(t) for t in theorems]

    # --- split-by-source summary (honesty rule: never merge sources) ---------
    by_source = defaultdict(lambda: defaultdict(int))
    source_totals = Counter()
    for r in public_records:
        src = r["source"]
        source_totals[src] += 1
        by_source[src][r["register"]] += 1

    split_summary = {
        src: {"total": source_totals[src], "by_register": dict(sorted(regs.items()))}
        for src, regs in sorted(by_source.items())
    }

    overall_by_register = Counter(r["register"] for r in public_records)

    public_doc = {
        "schema": "brockian-public-verified-registry/v1",
        "note": (
            "SANITIZED public surface. Counts are split by source; a headline "
            "count never merges 'we proved' (brockian/AXLE) with indexed "
            "sources. Internal run ids, review notes, hold markers and file "
            "paths are stripped."
        ),
        "generated_from": "registry/theorems.json (Brockian source of truth)",
        "public_fields": sorted(
            {
                "name", "module", "register", "kind", "statement",
                "conditional_rung", "discharged_by", "axioms", "axioms_ok",
                "axle_verdict", "env", "sorry_free", "source", "verified_by",
            }
        ),
        "summary": {
            "total": len(public_records),
            "by_source": split_summary,
            "by_register": dict(sorted(overall_by_register.items())),
        },
        "theorems": public_records,
    }

    os.makedirs(OUT_DIR, exist_ok=True)
    with open(OUT_PATH, "w", encoding="utf-8") as fh:
        json.dump(public_doc, fh, indent=2, ensure_ascii=False)
        fh.write("\n")

    # --- report --------------------------------------------------------------
    out_size = os.path.getsize(OUT_PATH)
    kept_top_level = sorted(all_input_fields & ALLOWED_INTERNAL_FIELDS)
    stripped_top_level = sorted(all_input_fields - ALLOWED_INTERNAL_FIELDS)
    # Sub-field strips (not top-level fields, so report explicitly):
    subfield_strips = [
        "source.file (internal path)",
        "verification.lake_build (internal build status)",
        "flags.native_decide / flags.exact_search (raw flags; only sorry_free derived)",
    ]

    print("=" * 68)
    print("SANITIZED PUBLIC REGISTRY EXPORT")
    print("=" * 68)
    print(f"input : {os.path.relpath(IN_PATH, _REPO)}  ({len(theorems)} records)")
    print(f"output: {os.path.relpath(OUT_PATH, _REPO)}  ({out_size:,} bytes)")
    print()
    print("KEPT internal top-level fields (allowlisted):")
    for f in kept_top_level:
        print(f"  + {f}")
    print()
    print("STRIPPED internal top-level fields (not on allowlist):")
    for f in stripped_top_level:
        marker = " [explicit sensitive]" if f in STRIPPED_INTERNAL_FIELDS else ""
        print(f"  - {f}{marker}")
    print()
    print("STRIPPED sub-fields (nested; verified below):")
    for f in subfield_strips:
        print(f"  - {f}")
    print()
    print("Public record fields emitted:")
    for f in public_doc["public_fields"]:
        print(f"  = {f}")
    print()
    print("SPLIT-BY-SOURCE summary (never merged):")
    for src, blk in split_summary.items():
        print(f"  [{src}] total={blk['total']}  {blk['by_register']}")
    print()
    print(f"overall by_register: {public_doc['summary']['by_register']}")
    print(f"total public records: {public_doc['summary']['total']}")

    # --- self-check: prove sensitive fields are absent from the RECORDS ------
    # Scan the serialized theorem records only (not the doc-level descriptive
    # note, which legitimately names the fields it strips).
    records_raw = json.dumps(public_records, ensure_ascii=False)
    leaks = []
    for token in ("ledger_run", "provenance_note", "quarantine", "lake_build"):
        if token in records_raw:
            leaks.append(token)
    # Any internal file path leak? public records must not carry .lean paths in a "file" facet.
    if '"file"' in records_raw or ".lean" in records_raw:
        leaks.append("file path (.lean / 'file' key)")
    print()
    if leaks:
        print(f"HONESTY CHECK FAILED -- sensitive tokens present: {leaks}", file=sys.stderr)
        return 2
    print("HONESTY CHECK PASSED: no ledger_run / provenance_note / quarantine / "
          "lake_build / file-path tokens in public output.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
