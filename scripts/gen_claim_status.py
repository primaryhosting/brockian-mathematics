#!/usr/bin/env python3
"""Generate the public claim-status table from the validated claim registry."""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

from validate_claims import DEFAULT_CLAIMS, validate_registry


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = ROOT / "docs" / "CLAIM_STATUS.md"


def _cell(value: str) -> str:
    return value.replace("|", "\\|").replace("\n", " ").strip()


def _hypotheses(claim: dict[str, Any]) -> str:
    values = []
    for item in claim["hypotheses_carried"]:
        values.append(f"`{item['name']}` — {item['range']}")
    return "; ".join(values) if values else "None"


def render(data: dict[str, Any]) -> str:
    lines = [
        "# Brockian claim-status table",
        "",
        "> Generated from `ledger/claims/claims.json`. This is an evidence and claim-boundary table, not a substitute for a Lean artifact or independent rerun.",
        "",
        "## Status legend",
        "",
        "- **Exact**: finite or algebraic statement as formulated.",
        "- **Standard**: established mathematics; the Brockian contribution is formalization, integration, or certified reuse.",
        "- **Conditional / Conjectural**: carries named hypothesis debt in the theorem statement; kernel axioms do not display those assumptions.",
        "- **V4** requires a pinned local build, source/signature hashes, and raw axiom report. **V5** also requires independent reproduction. No V0–V3 record may be described as final verified.",
        "",
        "## Claims",
        "",
        "| ID | Claim | Status / kind | Verification | Lean declaration | Explicit hypothesis debt |",
        "|---|---|---|---|---|---|",
    ]
    for claim in data["claims"]:
        lean = claim["lean"]["declaration"] or "—"
        lines.append(
            "| {id} | {title} | {status} / {kind} | {level} | {lean} | {hypotheses} |".format(
                id=_cell(claim["id"]),
                title=_cell(claim["title"]),
                status=_cell(claim["epistemic_status"]),
                kind=_cell(claim["result_kind"]),
                level=_cell(claim["verification_level"]),
                lean=_cell(lean),
                hypotheses=_cell(_hypotheses(claim)),
            )
        )
    lines.extend(["", "## Evidence records", ""])
    for claim in data["claims"]:
        lean = claim["lean"]
        lines.extend([
            f"### {claim['id']} — {claim['title']}",
            "",
            f"**Statement.** {claim['statement']}",
            "",
            f"**Scope.** {claim['scope']}",
            "",
            f"**Artifact.** `{lean['declaration'] or 'none'}` · `{lean['source_path'] or 'none'}` · local build: **{lean['local_build']}** · independent check: **{lean['independent_check']}**.",
            "",
            f"**Prior art / boundary.** {claim['provenance']['prior_art']} {claim['provenance']['notes']}",
            "",
            f"**Failure condition.** {claim['falsifier_or_failure_mode']}",
            "",
            f"**Approved public wording.** {claim['public_wording']}",
            "",
        ])
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--claims", type=Path, default=DEFAULT_CLAIMS)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    try:
        data = json.loads(args.claims.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        print(f"claims registry unreadable: {exc}", file=sys.stderr)
        return 2
    errors = validate_registry(data)
    if errors:
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(render(data))
    print(f"generated {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
