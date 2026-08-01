#!/usr/bin/env python3
"""Generate observatory/claims.yaml from registry/theorems.json + claim_map.yaml.

The register for every linked Lean declaration is DERIVED from the registry —
never hand-asserted in the claim map. Book badge labels are a presentation layer
over the same four registers used by the Lean program.

Usage:
    python3 scripts/gen_claims.py
    python3 scripts/gen_claims.py --registry registry/theorems.json \\
        --map observatory/claim_map.yaml --out observatory/claims.yaml
"""
from __future__ import annotations

import argparse
import json
import os
from datetime import datetime, timezone
from typing import Any

try:
    import yaml
except ImportError as e:  # pragma: no cover
    raise SystemExit("PyYAML required: pip install pyyaml") from e


# Book / Observatory presentation badges (map from derived register + force)
BOOK_BADGE = {
    "PROVED": "V3-LEAN-RUN",
    "CONDITIONAL": "CONDITIONAL",
    "CONJECTURE": "CONJECTURE",
    "DEFINITION": "DEFINITION",
    "COMPUTATION": "V2-INDEP-COMPUTED",
    "UNVERIFIED": "UNVERIFIED",
    "not_claimed": "NOT-CLAIMED",
    "prose": "V0-PROSE",
    "empirical": "V2-INDEP-COMPUTED",
    "open": "OPEN",
    "aristotle": "ARISTOTLE-PENDING",
}


def load_registry(path: str) -> dict[str, Any]:
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def index_by_name(reg: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {e["name"]: e for e in reg.get("theorems", [])}


def resolve_claim(
    claim: dict[str, Any],
    by_name: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    lean_names: list[str] = list(claim.get("lean") or [])
    decls: list[dict[str, Any]] = []
    missing: list[str] = []
    registers: list[str] = []

    for name in lean_names:
        e = by_name.get(name)
        if e is None:
            # try suffix match (short name unique?)
            short = name.split(".")[-1]
            matches = [v for k, v in by_name.items() if k.endswith("." + short) or k == short]
            if len(matches) == 1:
                e = matches[0]
                name = e["name"]
            else:
                missing.append(name)
                continue
        reg = e["register"]
        registers.append(reg)
        decls.append({
            "name": e["name"],
            "short": e["name"].split(".")[-1],
            "module": e.get("module") or "",
            "kind": e.get("kind"),
            "register": reg,
            "source": (e.get("source") or {}).get("file", ""),
            "axioms_ok": (e.get("verification") or {}).get("axioms_ok"),
            "axle": (e.get("verification") or {}).get("axle", {}),
            "ledger_run": e.get("ledger_run"),
            "provenance_note": e.get("provenance_note"),
        })

    force = claim.get("badge_force")
    if force:
        status = force
        book_badge = BOOK_BADGE.get(force, force.upper())
        derived_register = None
    elif not decls and not lean_names:
        status = "not_claimed"
        book_badge = BOOK_BADGE["not_claimed"]
        derived_register = None
    elif missing and not decls:
        status = "unmapped"
        book_badge = "UNMAPPED"
        derived_register = None
    else:
        # Worst-to-best for multi-decl claims: if any PROVED and none worse for "headline"
        # Headline status = best register among theorems (ignore DEFINITION for headline)
        thm_regs = [d["register"] for d in decls if d["kind"] in ("theorem", "lemma")]
        def_regs = [d["register"] for d in decls if d["kind"] not in ("theorem", "lemma")]
        order = ["UNVERIFIED", "CONJECTURE", "CONDITIONAL", "COMPUTATION", "PROVED", "DEFINITION"]
        pool = thm_regs or def_regs or registers
        # Prefer strongest proven signal for display: max by order index among pool
        derived_register = max(pool, key=lambda r: order.index(r) if r in order else -1)
        # But if any CONDITIONAL theorem exists alongside PROVED scaffolding, headline CONDITIONAL
        if "CONDITIONAL" in thm_regs:
            derived_register = "CONDITIONAL"
        elif "CONJECTURE" in thm_regs or any(d["kind"] == "conjecture" or d["register"] == "CONJECTURE" for d in decls):
            if "PROVED" not in thm_regs:
                derived_register = "CONJECTURE"
        elif "PROVED" in thm_regs:
            derived_register = "PROVED"
        status = derived_register.lower() if derived_register else "unknown"
        book_badge = BOOK_BADGE.get(derived_register or "", "UNKNOWN")

    return {
        "id": claim["id"],
        "title": claim.get("title", claim["id"]),
        "book": claim.get("book", ""),
        "notes": claim.get("notes") or "",
        "status": status,
        "book_badge": book_badge,
        "derived_register": derived_register,
        "badge_force": force,
        "lean": lean_names,
        "declarations": decls,
        "missing_lean": missing,
        "declaration_count": len(decls),
        "proved_count": sum(1 for d in decls if d["register"] == "PROVED"),
    }


def build_claims_doc(
    reg: dict[str, Any],
    cmap: dict[str, Any],
) -> dict[str, Any]:
    by_name = index_by_name(reg)
    summary = reg.get("summary") or {}
    claims_out = [resolve_claim(c, by_name) for c in (cmap.get("claims") or [])]

    by_status: dict[str, int] = {}
    for c in claims_out:
        by_status[c["status"]] = by_status.get(c["status"], 0) + 1

    return {
        "generated_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "generated_from": {
            "registry": "registry/theorems.json",
            "claim_map": "observatory/claim_map.yaml",
            "registry_summary": summary,
        },
        "program": cmap.get("program", "Brockian Mathematics"),
        "charter": (cmap.get("charter") or "").strip(),
        "version": cmap.get("version", 1),
        "summary": {
            "claims": len(claims_out),
            "by_status": by_status,
            "registry": summary,
        },
        "claims": claims_out,
        # Full registry dump for machines that want every declaration
        "all_declarations": [
            {
                "name": e["name"],
                "module": e.get("module"),
                "register": e["register"],
                "kind": e.get("kind"),
                "source": (e.get("source") or {}).get("file"),
                "axle": (e.get("verification") or {}).get("axle"),
            }
            for e in reg.get("theorems", [])
        ],
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--registry", default="registry/theorems.json")
    ap.add_argument("--map", default="observatory/claim_map.yaml")
    ap.add_argument("--out", default="observatory/claims.yaml")
    ap.add_argument("--json-out", default="observatory/claims.json",
                    help="Also write JSON for the static page generator")
    args = ap.parse_args()

    if not os.path.exists(args.registry):
        raise SystemExit(f"missing registry: {args.registry} (run scripts/gen_registry.py first)")
    if not os.path.exists(args.map):
        raise SystemExit(f"missing claim map: {args.map}")

    reg = load_registry(args.registry)
    cmap = yaml.safe_load(open(args.map, encoding="utf-8")) or {}
    doc = build_claims_doc(reg, cmap)

    os.makedirs(os.path.dirname(args.out) or ".", exist_ok=True)
    with open(args.out, "w", encoding="utf-8") as f:
        yaml.dump(doc, f, default_flow_style=False, sort_keys=False, allow_unicode=True)
    with open(args.json_out, "w", encoding="utf-8") as f:
        json.dump(doc, f, indent=2)

    s = doc["summary"]
    print(f"claims: {s['claims']} → {args.out} + {args.json_out}")
    print(f"  by_status: {s['by_status']}")
    print(f"  registry: {s['registry']}")
    missing = [c["id"] for c in doc["claims"] if c.get("missing_lean")]
    if missing:
        print(f"  WARNING missing lean links: {missing}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
