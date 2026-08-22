#!/usr/bin/env python3
"""Validate the Brockian claim registry without third-party dependencies.

This is intentionally stricter than the display generator. A public table may only
be generated from records whose verification level, explicit hypothesis debt, and
evidence fields agree. It does not infer mathematical truth from a label.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CLAIMS = ROOT / "ledger" / "claims" / "claims.json"

CLAIM_ID = re.compile(r"^BM-[A-Z0-9]+-[0-9]{3}-v[0-9]+\.[0-9]+$")
LEVELS = {"V0", "V1", "V2", "V3", "V4", "V5"}
CONDITIONAL = {"Conditional", "Conjectural", "Speculative"}
FORBIDDEN_ACTIVE_TERMS = {
    "BVPrimePairAsymptotic",
    "HL/BV",
    "Hardy-Littlewood / Bombieri-Vinogradov form",
    "Hardy–Littlewood / Bombieri–Vinogradov form",
}


def _error(errors: list[str], claim_id: str, message: str) -> None:
    errors.append(f"{claim_id}: {message}")


def validate_registry(data: dict[str, Any]) -> list[str]:
    """Return all integrity errors; an empty list means the registry is valid."""
    errors: list[str] = []
    if data.get("schema_version") != "1.0":
        errors.append("registry: schema_version must be '1.0'")
    claims = data.get("claims")
    if not isinstance(claims, list):
        return errors + ["registry: claims must be a list"]

    seen: set[str] = set()
    for claim in claims:
        if not isinstance(claim, dict):
            errors.append("registry: every claim must be an object")
            continue
        cid = claim.get("id", "<missing-id>")
        if not isinstance(cid, str) or not CLAIM_ID.fullmatch(cid):
            _error(errors, str(cid), "invalid claim ID")
        if cid in seen:
            _error(errors, str(cid), "duplicate claim ID")
        seen.add(cid)

        for field in (
            "title", "epistemic_status", "result_kind", "verification_level",
            "statement", "scope", "lean", "hypotheses_carried", "axioms_consumed",
            "provenance", "falsifier_or_failure_mode", "public_wording",
            "correction_history",
        ):
            if field not in claim:
                _error(errors, str(cid), f"missing required field {field!r}")

        level = claim.get("verification_level")
        if level not in LEVELS:
            _error(errors, str(cid), f"unknown verification level {level!r}")

        hypotheses = claim.get("hypotheses_carried")
        if not isinstance(hypotheses, list):
            _error(errors, str(cid), "hypotheses_carried must be a list")
            hypotheses = []
        if claim.get("epistemic_status") in CONDITIONAL and not hypotheses:
            _error(errors, str(cid), "conditional/conjectural claim has no explicit hypothesis debt")
        for hypothesis in hypotheses:
            if not isinstance(hypothesis, dict):
                _error(errors, str(cid), "hypothesis record must be an object")
                continue
            for field in ("name", "status", "range", "description"):
                if not hypothesis.get(field):
                    _error(errors, str(cid), f"hypothesis missing {field!r}")
            if hypothesis.get("name") == "Brockian.Hypothesis.UniformPrimePairsInAP":
                text = str(hypothesis.get("range", ""))
                if "Q" not in text or "q" not in text:
                    _error(errors, str(cid), "uniform AP hypothesis must state its q <= Q(X) range")

        lean = claim.get("lean")
        if not isinstance(lean, dict):
            _error(errors, str(cid), "lean evidence must be an object")
            lean = {}
        if level in {"V4", "V5"}:
            for field in ("declaration", "source_path", "source_hash", "theorem_signature_hash", "environment", "axiom_report_hash"):
                if not lean.get(field):
                    _error(errors, str(cid), f"{level} requires lean.{field}")
            if lean.get("local_build") != "pass":
                _error(errors, str(cid), f"{level} requires a passing pinned local build")
        if level == "V5" and lean.get("independent_check") != "pass":
            _error(errors, str(cid), "V5 requires an independent passing reproduction")

        active_surface = " ".join(
            str(claim.get(field, "")) for field in ("title", "statement", "scope", "public_wording")
        )
        for term in FORBIDDEN_ACTIVE_TERMS:
            if term in active_surface:
                _error(errors, str(cid), f"deprecated active terminology {term!r}")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--claims", type=Path, default=DEFAULT_CLAIMS)
    args = parser.parse_args()
    try:
        data = json.loads(args.claims.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        print(f"claims registry unreadable: {exc}", file=sys.stderr)
        return 2
    errors = validate_registry(data)
    if errors:
        print("claim registry INVALID:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    print(f"claim registry valid: {len(data['claims'])} records")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
