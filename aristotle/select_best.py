#!/usr/bin/env python3
"""Select the best surviving Aristotle candidate for every target.

The selector is deliberately verification-aware but never treats provenance as proof.
An AXLE or axiom-audit receipt applies only when its content hash matches the candidate.
A rejected winner is ranked behind every untested alternative on the next pass, so an
hourly harvest naturally advances through the candidate pool instead of getting stuck.

Writes ``best_proofs/<sanitized_target>.lean`` and a backwards-compatible manifest with
the complete ranked alternative list and the reason for the winning choice.
"""
from __future__ import annotations

import glob
import json
import pathlib
import re
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parent
REPO = ROOT.parent
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from engine.verify import content_hash  # noqa: E402

H = ROOT / "harvest_100"
LEDGER = ROOT / "harvest_ledger.json"
VSTATE = H / "verify_state.json"
AXLE = ROOT / "axle_verify.json"
AXIOMS = ROOT / "axle_axiom_audit.json"
OUT = ROOT / "best_proofs"
BAD = re.compile(r"\b(sorry|admit|native_decide|sorryAx)\b")


def safe_target(target: str) -> str:
    return re.sub(r"[^A-Za-z0-9]+", "_", target).strip("_")


def candidate_gate(
    proof_hash: str,
    axle_receipt: dict[str, Any] | None,
    axiom_receipt: dict[str, Any] | None,
) -> str:
    """Return ``verified``, ``unknown``, or ``rejected`` for this exact content.

    Stale receipts are ignored. Verification is fail-closed: both independent receipts
    must match and be positive before a candidate earns ``verified``.
    """

    axle_matches = bool(axle_receipt and axle_receipt.get("hash") == proof_hash)
    axiom_matches = bool(axiom_receipt and axiom_receipt.get("hash") == proof_hash)

    if axle_matches and axle_receipt.get("verified") is False:
        return "rejected"
    if axiom_matches and axiom_receipt.get("trusted") is False:
        return "rejected"
    if (
        axle_matches
        and axiom_matches
        and axle_receipt.get("verified") is True
        and axiom_receipt.get("trusted") is True
    ):
        return "verified"
    return "unknown"


def candidate_score(candidate: dict[str, Any]) -> tuple[Any, ...]:
    """Stable quality order; lower is better.

    Verified content wins, then untested content, then hash-matched rejected content.
    Within a gate, prefer local compile evidence, a clean lexical screen, and brevity.
    The project id makes otherwise identical races deterministic.
    """

    gate_rank = {"verified": 0, "unknown": 1, "rejected": 2}
    compile_rank = {True: 0, None: 1, False: 2}
    return (
        gate_rank.get(candidate.get("gate"), 3),
        compile_rank.get(candidate.get("compiles"), 3),
        0 if candidate.get("axiom_clean") else 1,
        candidate.get("lines", 10**9),
        candidate.get("project_id", ""),
    )


def selection_reason(candidate: dict[str, Any]) -> str:
    gate = candidate["gate"]
    if gate == "verified":
        return "hash-matched AXLE compile and axiom receipts"
    if gate == "unknown":
        return "best untested survivor; verification still required"
    return "no unrejected candidate remains; retained for diagnosis only"


def main():
    OUT.mkdir(exist_ok=True)
    ledger = json.loads(LEDGER.read_text()) if LEDGER.exists() else {}
    vstate = json.loads(VSTATE.read_text()) if VSTATE.exists() else {}
    axle = json.loads(AXLE.read_text()) if AXLE.exists() else {}
    axioms = json.loads(AXIOMS.read_text()) if AXIOMS.exists() else {}
    compiles = {b: s.get("compiles") for b, s in vstate.items()}

    # gather candidate proofs per target
    by_target = {}
    for pid, meta in ledger.items():
        if meta.get("verdict") != "PROVED":
            continue
        f = H / f"{meta['account']}_{pid[:8]}.lean"
        if not f.exists():
            continue
        text = f.read_text(errors="ignore")
        body = "\n".join(l for l in text.splitlines() if not l.strip().startswith("--"))
        key = f"{safe_target(meta['target'])}.lean"
        proof_hash = content_hash(text)
        cand = {
            "file": f,
            "account": meta["account"],
            "project_id": pid,
            "lines": len(text.splitlines()),
            "axiom_clean": not BAD.search(body),
            "compiles": compiles.get(f.name),
            "hash": proof_hash,
            "gate": candidate_gate(proof_hash, axle.get(key), axioms.get(key)),
        }
        by_target.setdefault(meta["target"], []).append(cand)

    manifest = {}
    for target, cands in by_target.items():
        ranked = sorted(cands, key=candidate_score)
        best = ranked[0]
        safe = safe_target(target)
        (OUT / f"{safe}.lean").write_text(best["file"].read_text(errors="ignore"))
        manifest[target] = {
            "chosen": best["file"].name,
            "account": best["account"],
            "project_id": best["project_id"],
            "lines": best["lines"],
            "axiom_clean": best["axiom_clean"],
            "compiles": best["compiles"],
            "n_candidates": len(cands),
            "chosen_hash": best["hash"],
            "winner_gate": best["gate"],
            "selection_reason": selection_reason(best),
            "alternatives": [
                {
                    "rank": rank,
                    "file": candidate["file"].name,
                    "account": candidate["account"],
                    "project_id": candidate["project_id"],
                    "lines": candidate["lines"],
                    "axiom_clean": candidate["axiom_clean"],
                    "compiles": candidate["compiles"],
                    "hash": candidate["hash"],
                    "gate": candidate["gate"],
                }
                for rank, candidate in enumerate(ranked, start=1)
            ],
        }
    (OUT / "manifest.json").write_text(json.dumps(manifest, indent=1, sort_keys=True))
    print(f"selected best proof for {len(manifest)} targets "
          f"(from {sum(len(v) for v in by_target.values())} candidates)")


if __name__ == "__main__":
    main()
