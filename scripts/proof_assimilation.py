#!/usr/bin/env python3
"""Compare proof attempts, surface promotion work, and steer the next targets.

This is a read-only control-plane join over the Aristotle harvest ledger, the
selected-proof manifest, the hash-bound AXLE/axiom results, the canonical registry,
and the frontier queue.  It never edits Lean source or the theorem registry.

Trust and utility stay deliberately separate:

* a proof is promotion-ready only after statement fidelity, AXLE, axiom, and local
  Lean gates are all explicitly green;
* backend provenance never makes a proof count;
* target priority rewards downstream unlocks and reuse, not theorem volume alone.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import re
from collections import Counter, defaultdict
from pathlib import Path
from statistics import median
from typing import Any, Iterable


REPO = Path(__file__).resolve().parent.parent
DEFAULTS = {
    "ledger": REPO / "aristotle" / "harvest_ledger.json",
    "best": REPO / "aristotle" / "best_proofs" / "manifest.json",
    "axle": REPO / "aristotle" / "axle_verify.json",
    "axioms": REPO / "aristotle" / "axle_axiom_audit.json",
    "registry": REPO / "registry" / "theorems.json",
    "frontier": REPO / "research" / "frontier_queue.json",
    "output": REPO / "research" / "proof_assimilation.json",
    "review": REPO / "research" / "proof_assimilation.REVIEW.md",
}

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TERMINAL_CANDIDATE = {"PROVED", "COMPLETE", "COMPLETE_WITH_ERRORS", "IDLE"}
NEGATIVE_VERDICTS = {"REFUTED", "DISPROVED", "COUNTEREXAMPLE"}
REJECTED_VERDICTS = {"STOPPED", "FAILED", "ERROR", "CANCELLED", "REJECTED"}
FOUNDATION_CLASSES = {
    "api", "api-design", "bridge", "foundation", "infrastructure", "parser",
    "transfer", "library",
}


def load_json(path: os.PathLike[str] | str, default: Any) -> Any:
    path = Path(path)
    if not path.exists():
        return default
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def safe_target(target: str) -> str:
    return re.sub(r"[^A-Za-z0-9]+", "_", target).strip("_")


def _state_record(state: dict[str, Any], target: str) -> dict[str, Any]:
    return state.get(safe_target(target) + ".lean", {})


def _bool(value: Any) -> bool | None:
    if value is True or str(value).lower() in {"true", "ok", "passed", "verified"}:
        return True
    if value is False or str(value).lower() in {"false", "failed", "rejected"}:
        return False
    return None


def candidate_gate(candidate: dict[str, Any]) -> str:
    """Return a fail-closed gate state for one proof attempt."""
    verdict = str(candidate.get("verdict") or candidate.get("status") or "").upper()
    if verdict in REJECTED_VERDICTS:
        return "rejected"
    if candidate.get("statement_hash_ok") is False or candidate.get("faithful") is False:
        return "rejected"
    if candidate.get("has_forbidden_token") or candidate.get("sorry"):
        return "rejected"
    axioms = set(candidate.get("axioms") or [])
    if axioms - ALLOWED_AXIOMS or "sorryAx" in axioms:
        return "rejected"
    axle = _bool(candidate.get("axle_verified"))
    axiom = _bool(candidate.get("axiom_trusted"))
    local = _bool(candidate.get("local_lean"))
    if axle is False or axiom is False or local is False:
        return "rejected"
    if axle is True and axiom is True and local is True:
        return "promotion_ready"
    if axle is True and axiom is True:
        return "attested_pending_local"
    if verdict in TERMINAL_CANDIDATE:
        return "proof_candidate"
    if verdict in NEGATIVE_VERDICTS:
        return "negative_candidate"
    return "pending"


def build_candidates(
    ledger: dict[str, Any],
    best: dict[str, Any],
    axle_state: dict[str, Any],
    axiom_state: dict[str, Any],
) -> list[dict[str, Any]]:
    """Join hourly Aristotle attempts to the chosen proof and its verification legs."""
    candidates: list[dict[str, Any]] = []
    for project_id, raw in ledger.items():
        if not isinstance(raw, dict):
            continue
        target = str(raw.get("target") or raw.get("name") or "").strip()
        if not target:
            continue
        picked = best.get(target) if isinstance(best.get(target), dict) else {}
        chosen = str(picked.get("project_id") or "") == str(project_id)
        candidate = {
            "project_id": str(project_id),
            "target": target,
            "backend": str(raw.get("backend") or raw.get("engine") or "aristotle"),
            "account": raw.get("account"),
            "tier": raw.get("tier"),
            "verdict": str(raw.get("verdict") or raw.get("status") or "UNKNOWN").upper(),
            "chosen": chosen,
            "lines": raw.get("lines"),
            "latency_s": raw.get("latency_s"),
            "cost_usd": raw.get("cost_usd"),
            "finished_at": raw.get("finished_at") or raw.get("completed_at"),
            "polarity": raw.get("polarity"),
            "statement_hash_ok": raw.get("statement_hash_ok"),
            "faithful": raw.get("faithful"),
            "has_forbidden_token": raw.get("has_forbidden_token", False),
        }
        if chosen:
            candidate["lines"] = picked.get("lines", candidate["lines"])
            candidate["local_lean"] = picked.get("compiles")
            candidate["proof_file"] = picked.get("chosen")
            ax = _state_record(axle_state, target)
            au = _state_record(axiom_state, target)
            candidate["axle_verified"] = ax.get("verified")
            candidate["axle_hash"] = ax.get("hash")
            candidate["axiom_trusted"] = au.get("trusted")
            candidate["axioms"] = au.get("axioms") or []
            candidate["axiom_hash"] = au.get("hash")
        candidate["gate"] = candidate_gate(candidate)
        candidates.append(candidate)
    return candidates


GATE_ORDER = {
    "promotion_ready": 0,
    "attested_pending_local": 1,
    "proof_candidate": 2,
    "pending": 3,
    "negative_candidate": 4,
    "rejected": 5,
}


def comparison_key(candidate: dict[str, Any]) -> tuple[Any, ...]:
    lines = candidate.get("lines")
    latency = candidate.get("latency_s")
    cost = candidate.get("cost_usd")
    return (
        GATE_ORDER.get(str(candidate.get("gate")), 9),
        0 if candidate.get("chosen") else 1,
        lines if isinstance(lines, (int, float)) else float("inf"),
        latency if isinstance(latency, (int, float)) else float("inf"),
        cost if isinstance(cost, (int, float)) else float("inf"),
        str(candidate.get("project_id") or ""),
    )


def group_candidates(
    candidates: Iterable[dict[str, Any]], registry_names: set[str]
) -> list[dict[str, Any]]:
    grouped: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for candidate in candidates:
        grouped[candidate["target"]].append(candidate)
    groups: list[dict[str, Any]] = []
    for target in sorted(grouped):
        attempts = sorted(grouped[target], key=comparison_key)
        polarities = {str(c["polarity"]).lower() for c in attempts if c.get("polarity")}
        has_positive = any(c.get("verdict") in TERMINAL_CANDIDATE for c in attempts)
        has_negative = any(c.get("verdict") in NEGATIVE_VERDICTS for c in attempts)
        disputed = len(polarities) > 1 or (has_positive and has_negative)
        winner = None if disputed else next(
            (c for c in attempts if c["gate"] != "rejected"), None
        )
        registered = target in registry_names
        if registered:
            action = "assimilated"
        elif disputed:
            action = "human_review_dispute"
        elif winner is None:
            action = "blocked_no_clean_candidate"
        elif winner["gate"] == "promotion_ready":
            action = "promote"
        elif winner["gate"] == "attested_pending_local":
            action = "local_verify"
        else:
            action = "verify"
        groups.append({
            "target": target,
            "registered": registered,
            "disputed": disputed,
            "attempt_count": len(attempts),
            "clean_candidate_count": sum(c["gate"] != "rejected" for c in attempts),
            "winner_project_id": winner.get("project_id") if winner else None,
            "winner_gate": winner.get("gate") if winner else None,
            "next_action": action,
            "attempts": attempts,
        })
    return groups


def _countish(value: Any) -> int:
    if isinstance(value, list):
        return len(value)
    if isinstance(value, dict):
        return len(value)
    if isinstance(value, (int, float)):
        return max(0, int(value))
    return 0


def _target_name(entry: dict[str, Any]) -> str:
    lean_target = entry.get("lean_target") or {}
    return str(lean_target.get("name") or entry.get("target") or entry.get("statement") or "")


def _frontier_from_registry(registry: dict[str, Any]) -> list[dict[str, Any]]:
    entries = []
    for theorem in registry.get("theorems", []):
        if theorem.get("register") not in {"CONJECTURE", "CONDITIONAL"}:
            continue
        entries.append({
            "id": "registry:" + theorem.get("name", ""),
            "statement": theorem.get("statement") or theorem.get("name", ""),
            "lean_target": {"name": theorem.get("name", ""), "module": theorem.get("module", "")},
            "source": "registry-conjecture",
            "scores": {"legibility": 3, "tractability": 3, "novelty": 3},
            "status": "open",
        })
    return entries


def _backend_route(entry: dict[str, Any], action: str) -> str:
    if action in {"promote", "verify", "local_verify", "human_review_dispute"}:
        return "verification"
    stats = entry.get("backend_stats") or {}
    scored = []
    for backend, values in stats.items():
        submitted = int(values.get("submitted") or 0)
        clean = int(values.get("clean_proofs") or 0)
        if submitted < 3:
            continue
        rate = clean / submitted
        latency = float(values.get("median_latency_s") or 1e12)
        scored.append((rate, -latency, backend))
    if len(scored) >= 2:
        scored.sort(reverse=True)
        if scored[0][0] - scored[1][0] >= 0.15:
            return scored[0][2]
        return "race"
    target_class = str(entry.get("target_class") or "").lower()
    if target_class in {"harness", "parser", "api-design", "integration"}:
        return "codex"
    return "race"


def score_frontier(
    frontier: dict[str, Any],
    registry: dict[str, Any],
    groups: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    entries = list(frontier.get("entries") or _frontier_from_registry(registry))
    registry_names = {
        t.get("name") for t in registry.get("theorems", []) if t.get("register") == "PROVED"
    }
    by_target = {g["target"]: g for g in groups}
    dependents: Counter[str] = Counter()
    for entry in entries:
        for dep in entry.get("depends_on") or []:
            dependents[str(dep)] += 1

    ranked = []
    for entry in entries:
        if entry.get("status") in {"proved", "refuted", "stale"}:
            continue
        target = _target_name(entry)
        if not target or target in registry_names:
            continue
        scores = entry.get("scores") or {}
        base = 3 * int(scores.get("legibility", 0)) + 2 * int(scores.get("tractability", 0)) + int(scores.get("novelty", 0))
        compounding = entry.get("compounding") or {}
        unlocks = max(_countish(entry.get("unlocks")), _countish(compounding.get("unlocks")), dependents[target])
        consumers = max(_countish(entry.get("consumers")), _countish(compounding.get("consumers")))
        dependencies = [str(v) for v in (entry.get("depends_on") or compounding.get("depends_on") or [])]
        blocked = [dep for dep in dependencies if dep not in registry_names]
        target_class = str(entry.get("target_class") or compounding.get("target_class") or "").lower()
        foundation = bool(entry.get("foundational") or compounding.get("foundational") or target_class in FOUNDATION_CLASSES)
        group = by_target.get(target)
        group_action = group.get("next_action") if group else None
        proof_bonus = {"promote": 14, "local_verify": 11, "verify": 7}.get(group_action, 0)
        failure_count = int(entry.get("failed_attempts") or compounding.get("failed_attempts") or 0)
        cost = float(entry.get("estimated_cost_usd") or compounding.get("estimated_cost_usd") or 0)
        breakdown = {
            "editorial_base": base,
            "downstream_unlocks": min(24, 4 * unlocks),
            "known_consumers": min(12, 2 * consumers),
            "foundation_bonus": 5 if foundation else 0,
            "proof_in_hand_bonus": proof_bonus,
            "dependencies_ready": 4 if dependencies and not blocked else 0,
            "blocked_dependency_penalty": -min(18, 6 * len(blocked)),
            "failed_attempt_penalty": -min(8, 2 * failure_count),
            "estimated_cost_penalty": -min(10, int(cost / 4)),
        }
        total = sum(breakdown.values())
        if group_action in {"promote", "local_verify", "verify", "human_review_dispute"}:
            action = group_action
        elif blocked:
            action = "prove_dependency"
        else:
            action = "proof_search"
        ranked.append({
            "frontier_id": entry.get("id"),
            "target": target,
            "statement": entry.get("statement") or target,
            "status": entry.get("status", "open"),
            "source": entry.get("source"),
            "target_class": target_class or None,
            "compounding_score": total,
            "score_breakdown": breakdown,
            "unlocks": unlocks,
            "consumers": consumers,
            "blocked_by": blocked,
            "proof_attempts_in_hand": group.get("attempt_count", 0) if group else 0,
            "recommended_action": action,
            "recommended_backend": _backend_route(entry, action),
        })
    ranked.sort(key=lambda row: (-row["compounding_score"], str(row["frontier_id"] or row["target"])))
    for rank, row in enumerate(ranked, 1):
        row["steering_rank"] = rank
    return ranked


def backend_performance(candidates: Iterable[dict[str, Any]]) -> dict[str, Any]:
    buckets: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for candidate in candidates:
        buckets[str(candidate.get("backend") or "unknown")].append(candidate)
    result = {}
    for backend, rows in sorted(buckets.items()):
        clean = sum(r.get("gate") in {"promotion_ready", "attested_pending_local"} for r in rows)
        latencies = [float(r["latency_s"]) for r in rows if isinstance(r.get("latency_s"), (int, float))]
        result[backend] = {
            "attempts": len(rows),
            "clean_attested": clean,
            "clean_rate": round(clean / len(rows), 4) if rows else 0.0,
            "median_latency_s": median(latencies) if latencies else None,
        }
    return result


def throughput_per_hour(candidates: Iterable[dict[str, Any]], now: str, hours: int = 24) -> float | None:
    try:
        end = dt.datetime.fromisoformat(now.replace("Z", "+00:00"))
    except ValueError:
        return None
    count = 0
    saw_timestamp = False
    for candidate in candidates:
        raw = candidate.get("finished_at")
        if not raw:
            continue
        try:
            finished = dt.datetime.fromisoformat(str(raw).replace("Z", "+00:00"))
        except ValueError:
            continue
        saw_timestamp = True
        age = (end - finished).total_seconds()
        if 0 <= age <= hours * 3600:
            count += 1
    return round(count / hours, 4) if saw_timestamp else None


def build_report(
    *, ledger: dict[str, Any], best: dict[str, Any], axle: dict[str, Any], axioms: dict[str, Any],
    registry: dict[str, Any], frontier: dict[str, Any], now: str,
) -> dict[str, Any]:
    registry_names = {
        t.get("name") for t in registry.get("theorems", []) if t.get("register") == "PROVED"
    }
    candidates = build_candidates(ledger, best, axle, axioms)
    groups = group_candidates(candidates, registry_names)
    steering = score_frontier(frontier, registry, groups)
    gates = Counter(c["gate"] for c in candidates)
    return {
        "schema_version": 1,
        "generated_at": now,
        "trust_policy": {
            "promotion_requires": ["statement_fidelity", "AXLE", "clean_axioms", "local_lean"],
            "allowed_axioms": sorted(ALLOWED_AXIOMS),
            "provenance_affects_truth": False,
        },
        "summary": {
            "attempts": len(candidates),
            "targets_with_attempts": len(groups),
            "duplicate_attempts": sum(max(0, g["attempt_count"] - 1) for g in groups),
            "disputed_targets": sum(g["disputed"] for g in groups),
            "promotion_ready": gates["promotion_ready"],
            "attested_pending_local": gates["attested_pending_local"],
            "proof_candidates": gates["proof_candidate"],
            "rejected": gates["rejected"],
            "rolling_24h_attempts_per_hour": throughput_per_hour(candidates, now),
            "steerable_targets": len(steering),
        },
        "backend_performance": backend_performance(candidates),
        "proof_groups": groups,
        "steering_queue": steering,
    }


def render_markdown(report: dict[str, Any], limit: int = 30) -> str:
    summary = report["summary"]
    lines = [
        "# Proof Assimilation — review",
        "",
        f"Generated {report['generated_at']}",
        "",
        "## Intake",
        "",
        f"- Attempts: {summary['attempts']} across {summary['targets_with_attempts']} targets",
        f"- Duplicate attempts compared: {summary['duplicate_attempts']}",
        f"- Promotion-ready: {summary['promotion_ready']}",
        f"- AXLE/axiom clean but awaiting local Lean: {summary['attested_pending_local']}",
        f"- Disputed targets: {summary['disputed_targets']}",
        "",
        "## Promotion queue",
        "",
        "| target | attempts | winner gate | next action |",
        "|---|---:|---|---|",
    ]
    actionable = [g for g in report["proof_groups"] if g["next_action"] != "assimilated"]
    for group in actionable[:limit]:
        lines.append(
            f"| {group['target']} | {group['attempt_count']} | {group['winner_gate'] or '—'} | {group['next_action']} |"
        )
    lines += [
        "",
        "## Compounding-value steering",
        "",
        "| rank | score | target | unlocks | proofs in hand | action | backend |",
        "|---:|---:|---|---:|---:|---|---|",
    ]
    for row in report["steering_queue"][:limit]:
        lines.append(
            f"| {row['steering_rank']} | {row['compounding_score']} | {row['target']} | "
            f"{row['unlocks']} | {row['proof_attempts_in_hand']} | {row['recommended_action']} | "
            f"{row['recommended_backend']} |"
        )
    lines += [
        "",
        "The score is operational priority, not mathematical truth. Every promotion still requires all four trust gates.",
        "",
    ]
    return "\n".join(lines)


def write_json_atomic(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + ".tmp")
    with temp.open("w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, ensure_ascii=False, sort_keys=True)
        handle.write("\n")
    os.replace(temp, path)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("ledger", "best", "axle", "axioms", "registry", "frontier", "output", "review"):
        parser.add_argument("--" + name, default=str(DEFAULTS[name]))
    parser.add_argument("--now", default=None, help="ISO timestamp override for reproducible runs")
    args = parser.parse_args(argv)
    now = args.now or dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    report = build_report(
        ledger=load_json(args.ledger, {}),
        best=load_json(args.best, {}),
        axle=load_json(args.axle, {}),
        axioms=load_json(args.axioms, {}),
        registry=load_json(args.registry, {"theorems": []}),
        frontier=load_json(args.frontier, {"entries": []}),
        now=now,
    )
    write_json_atomic(Path(args.output), report)
    review = Path(args.review)
    review.parent.mkdir(parents=True, exist_ok=True)
    review.write_text(render_markdown(report), encoding="utf-8")
    print(
        "proof assimilation: "
        f"{report['summary']['attempts']} attempts, "
        f"{report['summary']['promotion_ready']} promotion-ready, "
        f"{report['summary']['steerable_targets']} steerable targets"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
