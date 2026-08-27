#!/usr/bin/env python3
"""Aristotle Command Dashboard — data generator.

Reads the conveyor's ledger/verification/selection artifacts (read-only) and emits
``aristotle/dashboard_data.json`` per the data contract in
``docs/superpowers/specs/2026-08-27-aristotle-dashboard-design.md`` (binding).

Design constraints (from the spec/plan):
- stdlib only; pure functions are time-free (the CLI layer stamps ``generated_at``);
- strictly read-only against all input files;
- per-section degradation: a missing/corrupt input nulls its section and appends a
  warning — the build never aborts over one file (exit 0);
- honesty rules: Aristotle-internal PROVED != independently attested; ``verified:
  false`` AXLE results surface as ``verify_failed``; missing data is null + warning,
  never fabricated zeros.
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter, defaultdict
from datetime import datetime, timedelta, timezone
from pathlib import Path

REPO = "primaryhosting/brockian-mathematics"
BRANCH = "conveyor/2026-08-18"
GITHUB_BLOB_BASE = f"https://github.com/{REPO}/blob/{BRANCH}/aristotle/best_proofs/"

# Stage ordering (max wins per target) — spec "Derivation rules (binding)".
STAGE_RANK = {
    "attested": 6,
    "verified": 5,
    "verify_failed": 4,
    "selected": 3,
    "candidate": 2,
    "in_flight": 1,
    "stopped": 0,
}

PREVIEW_LINES = 20
RECENT_EVENTS = 50
STALE_DAYS = 7
ORPHAN_LIST_CAP = 20

RIEMANN_WARNING = "riemann: no per-theorem table; publish path is phase 2"


# --------------------------------------------------------------------------- pure


def load_ledger(path) -> dict:
    """uuid -> {target, account, verdict, tier, ...extra fields tolerated}."""
    with open(path) as fh:
        data = json.load(fh)
    if not isinstance(data, dict):
        raise ValueError("harvest_ledger.json: expected dict keyed by project uuid")
    return data


def domain_of(target: str) -> str:
    """Namespace prefix is the domain dimension; no dot -> '(root)'."""
    return target.split(".", 1)[0] if "." in target else "(root)"


def mangle(target: str) -> str:
    """Ledger dot-name -> best_proofs/axle filename stem (dots -> underscores)."""
    return target.replace(".", "_")


def parse_night_log(lines) -> list:
    """Parse ``TS OK acct Target -> uuid`` / ``TS FAIL acct Target (reason)`` lines.

    Anything else (tracebacks, blanks) is skipped.
    """
    events = []
    for line in lines:
        parts = line.split()
        if len(parts) < 4 or parts[1] not in ("OK", "FAIL"):
            continue
        event = {
            "ts": parts[0],
            "status": parts[1],
            "account": parts[2],
            "target": parts[3],
        }
        rest = parts[4:]
        if parts[1] == "OK" and len(rest) >= 2 and rest[0] == "->":
            event["project_id"] = rest[1]
            event["detail"] = None
        else:
            event["project_id"] = None
            event["detail"] = " ".join(rest) or None
        events.append(event)
    return events


def find_inflight(ledger: dict, submitted_night: dict, log_events: list) -> set:
    """Targets with >=1 submission id absent from the ledger (spec: solver_state is
    stale and is NOT used for this)."""
    known = set(ledger)
    inflight = set()
    for target, info in (submitted_night or {}).items():
        for rec in info.get("ids", []):
            if rec.get("project_id") and rec["project_id"] not in known:
                inflight.add(target)
                break
    for event in log_events or []:
        if event.get("project_id") and event["project_id"] not in known:
            inflight.add(event["target"])
    return inflight


def build_targets(ledger, axle, best_files, registry_names, inflight_targets):
    """ONE ROW PER UNIQUE TARGET — the corpus ledger.

    Returns ``(rows, warnings)``. ``axle`` may be None (missing input): stages then
    degrade past the verified/verify_failed rungs and a warning is emitted by the
    caller-facing path (see ``main``); orphan axle keys / best-proof files matching
    no target are counted + listed in warnings and excluded from funnel counts.
    """
    warnings = []
    if axle is None:
        warnings.append("axle results missing — verified/verify_failed stages "
                        "unavailable for all targets")
        axle = {}
    best_files = best_files or set()
    registry_names = registry_names or set()
    inflight_targets = inflight_targets or set()

    grouped = defaultdict(list)
    for entry in ledger.values():
        grouped[entry["target"]].append(entry)

    file_of = {mangle(t) + ".lean": t for t in
               set(grouped) | set(inflight_targets)}

    orphan_axle = sorted(set(axle) - set(file_of))
    if orphan_axle:
        warnings.append(
            "orphan axle entries (no matching pipeline target), excluded from "
            "funnel: %d — %s" % (len(orphan_axle),
                                 ", ".join(orphan_axle[:ORPHAN_LIST_CAP])))
    orphan_best = sorted(set(best_files) - set(file_of))
    if orphan_best:
        warnings.append(
            "orphan best_proofs files (no matching pipeline target), excluded "
            "from funnel: %d — %s" % (len(orphan_best),
                                      ", ".join(orphan_best[:ORPHAN_LIST_CAP])))

    rows = []
    for target in sorted(set(grouped) | set(inflight_targets)):
        entries = grouped.get(target, [])
        fname = mangle(target) + ".lean"
        in_best = fname in best_files
        axle_rec = axle.get(fname)

        rank = 0  # stopped
        if target in inflight_targets:
            rank = max(rank, STAGE_RANK["in_flight"])
        if any(e.get("verdict") == "PROVED" for e in entries):
            rank = max(rank, STAGE_RANK["candidate"])
        if in_best:
            rank = max(rank, STAGE_RANK["selected"])
        if axle_rec is not None:
            verified = axle_rec.get("verified")
            if verified is True:
                rank = max(rank, STAGE_RANK["verified"])
            elif verified is False:
                rank = max(rank, STAGE_RANK["verify_failed"])
            else:
                # spec: verified:null goes to warnings, not either bucket
                warnings.append(
                    "axle verified:null for %s — counted in neither "
                    "verified nor verify_failed" % fname)
        if target in registry_names:
            rank = max(rank, STAGE_RANK["attested"])
        stage = next(s for s, r in STAGE_RANK.items() if r == rank)

        certificate = None
        if in_best or axle_rec is not None:
            certificate = {
                "file": fname if in_best else None,
                "verified": axle_rec.get("verified") if axle_rec else None,
                "environment": axle_rec.get("environment") if axle_rec else None,
                "hash": axle_rec.get("hash") if axle_rec else None,
                "preview": None,
                "github_url": GITHUB_BLOB_BASE + fname if in_best else None,
            }

        rows.append({
            "target": target,
            "domain": domain_of(target),
            "tiers": sorted({e["tier"] for e in entries if e.get("tier")}),
            "submissions": len(entries),
            "accounts": dict(Counter(e["account"] for e in entries
                                     if e.get("account"))),
            "verdicts": dict(Counter(e["verdict"] for e in entries
                                     if e.get("verdict"))),
            "stage": stage,
            "certificate": certificate,
            "riemann_published": None,
        })
    return rows, warnings


def build_funnel(rows, ledger, missing=frozenset()) -> dict:
    """Joined-target counts (spec: raw file counts live in Health, not here).

    ``missing`` names unavailable inputs ({'axle','best','registry'}) whose funnel
    fields become None — honest nulls, never fabricated zeros.
    """
    verdicts = Counter(e.get("verdict") for e in ledger.values())
    certs = [r["certificate"] for r in rows if r["certificate"]]
    funnel = {
        "submissions": len(ledger),
        "unique_targets": len({e["target"] for e in ledger.values()}),
        "proved_candidates": verdicts.get("PROVED", 0),
        "stopped": verdicts.get("STOPPED", 0),
        "selected_best": (None if "best" in missing else
                          sum(1 for c in certs if c["file"])),
        "axle_verified": (None if "axle" in missing else
                          sum(1 for c in certs if c["verified"] is True)),
        "axle_failed": (None if "axle" in missing else
                        sum(1 for c in certs if c["verified"] is False)),
        "registry_attested": (None if "registry" in missing else
                              sum(1 for r in rows if r["stage"] == "attested")),
        "riemann_published": None,
    }
    return funnel


def funnel_warnings(funnel) -> list:
    """Nesting checks: by-construction-nested stages violated -> warning; the
    registry stage is NOT strictly nested (spec) so a crossover warns, never fails."""
    warnings = []

    def _num(key):
        value = funnel.get(key)
        return value if isinstance(value, (int, float)) else None

    chain = ["submissions", "unique_targets", "selected_best", "axle_verified"]
    for higher, lower in zip(chain, chain[1:]):
        h, l = _num(higher), _num(lower)
        if h is not None and l is not None and l > h:
            warnings.append("funnel non-monotonic: %s (%s) > %s (%s)"
                            % (lower, l, higher, h))
    reg, ver = _num("registry_attested"), _num("axle_verified")
    if reg is not None and ver is not None and reg > ver:
        warnings.append(
            "registry_attested (%d) exceeds axle_verified (%d) — registry and "
            "AXLE stages are not strictly nested (repo attestation path)"
            % (reg, ver))
    return warnings


def build_yield_matrix(ledger, verified_targets=frozenset()) -> list:
    """Per (domain, tier) cell; submissions deduped per (target, tier).

    Multi-tier targets appear in EVERY (domain, tier) cell they were submitted
    under (spec), so cell sums exceed unique totals.
    Rates are unique-target fractions within the cell:
    - proved_rate:  targets with >=1 PROVED submission under that tier;
    - stopped_rate: targets with 0 PROVED under that tier (all STOPPED);
    - verified_rate: targets that are AXLE-verified (verified: true join).
    """
    cells = defaultdict(lambda: defaultdict(lambda: {"proved": False, "seen": True}))
    for entry in ledger.values():
        cell = cells[(domain_of(entry["target"]), entry.get("tier"))]
        record = cell[entry["target"]]
        if entry.get("verdict") == "PROVED":
            record["proved"] = True
    matrix = []
    for (domain, tier), targets in sorted(cells.items()):
        unique = len(targets)
        proved = sum(1 for rec in targets.values() if rec["proved"])
        verified = sum(1 for t in targets if t in verified_targets)
        matrix.append({
            "domain": domain,
            "tier": tier,
            "unique": unique,
            "proved_rate": round(proved / unique, 4),
            "verified_rate": round(verified / unique, 4),
            "stopped_rate": round((unique - proved) / unique, 4),
        })
    return matrix


def rate_limit_count_24h(events, now=None) -> int:
    """RATE-backoff FAILs in the 24h before ``now`` (defaults to the max log
    timestamp so pure callers stay time-free)."""
    stamped = []
    for event in events:
        try:
            stamped.append((datetime.fromisoformat(event["ts"]), event))
        except (ValueError, TypeError):
            continue
    if not stamped:
        return 0
    if now is None:
        now = max(ts for ts, _ in stamped)
    cutoff = now - timedelta(hours=24)
    return sum(1 for ts, e in stamped
               if ts >= cutoff and e["status"] == "FAIL"
               and "RATE" in (e.get("detail") or ""))


def build_health(events, ledger, stale_files=None, raw_counts=None,
                 last_harvest_sync=None, now=None) -> dict:
    return {
        "recent_events": events[-RECENT_EVENTS:],
        "rate_limit_count_24h": rate_limit_count_24h(events, now=now),
        "account_split": dict(Counter(
            e["account"] for e in (ledger or {}).values() if e.get("account"))),
        "stale_files": stale_files or [],
        "raw_counts": raw_counts or {},
        "last_harvest_sync": last_harvest_sync,
    }


def attach_previews(rows, best_dir, max_lines=PREVIEW_LINES) -> None:
    """First ``max_lines`` lines, ONLY for joined ``verified: true`` targets."""
    best_dir = Path(best_dir)
    for row in rows:
        cert = row["certificate"]
        if not cert or cert["verified"] is not True or not cert["file"]:
            continue
        path = best_dir / cert["file"]
        try:
            with open(path, encoding="utf-8", errors="replace") as fh:
                lines = []
                for _ in range(max_lines):
                    line = fh.readline()
                    if not line:
                        break
                    lines.append(line.rstrip("\n"))
            cert["preview"] = "\n".join(lines)
        except OSError:
            continue


# ----------------------------------------------------------------------- CLI layer


def _try(warnings, section, fn):
    try:
        return fn()
    except Exception as exc:  # per-section degradation, never abort the build
        warnings.append("%s: unavailable (%s: %s)"
                        % (section, type(exc).__name__, exc))
        return None


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--generated-at", default=None,
                        help="ISO timestamp; defaults to UTC now (CLI layer only)")
    parser.add_argument("--out", default=None,
                        help="output path (default: aristotle/dashboard_data.json)")
    args = parser.parse_args(argv)

    base = Path(__file__).resolve().parent
    out_path = Path(args.out) if args.out else base / "dashboard_data.json"
    generated_at = args.generated_at or datetime.now(timezone.utc).isoformat()
    warnings = []

    ledger = _try(warnings, "harvest_ledger.json",
                  lambda: load_ledger(base / "harvest_ledger.json"))
    axle = _try(warnings, "axle_verify.json",
                lambda: json.load(open(base / "axle_verify.json")))
    submitted = _try(warnings, "submitted_night.json",
                     lambda: json.load(open(base / "submitted_night.json")))
    registry_names = _try(
        warnings, "registry/theorems.json",
        lambda: {t["name"] for t in
                 json.load(open(base.parent / "registry" / "theorems.json"))
                 ["theorems"] if isinstance(t, dict) and "name" in t})
    best_files = _try(
        warnings, "best_proofs/",
        lambda: {p.name for p in (base / "best_proofs").iterdir()
                 if p.suffix == ".lean"})
    log_lines = _try(
        warnings, "night_submit.log",
        lambda: open(base / "night_submit.log",
                     encoding="utf-8", errors="replace").readlines()) or []
    events = parse_night_log(log_lines)

    missing = {name for name, loaded in
               (("axle", axle), ("best", best_files), ("registry", registry_names))
               if loaded is None}

    rows = funnel = matrix = None
    if ledger is not None:
        inflight = find_inflight(ledger, submitted or {}, events)
        rows, row_warnings = build_targets(
            ledger, axle, best_files or set(), registry_names or set(), inflight)
        warnings.extend(row_warnings)
        _try(warnings, "lean previews",
             lambda: attach_previews(rows, base / "best_proofs"))
        funnel = build_funnel(rows, ledger, missing=missing)
        warnings.extend(funnel_warnings(funnel))
        verified_targets = {r["target"] for r in rows
                            if r["certificate"]
                            and r["certificate"]["verified"] is True}
        matrix = build_yield_matrix(ledger, verified_targets=verified_targets)

    # Staleness + known-bug warnings (mtime checks live here, not in pure fns).
    stale_files = []
    solver_state = base / "solver_state.json"
    if solver_state.exists():
        age_days = (time.time() - solver_state.stat().st_mtime) / 86400
        if age_days > STALE_DAYS:
            stale_files.append("solver_state.json (%.0fd)" % age_days)
    warnings.append(
        "solver_state.json is stale by content (all IDLE); NOT used for "
        "in_flight derivation")
    report = base / "harvest_report.md"
    if report.exists():
        try:
            if "-927" in report.read_text(errors="replace"):
                warnings.append("harvest_report counter bug (-927)")
        except OSError:
            pass
    warnings.extend(stale_files and
                    ["stale input file: %s" % s for s in stale_files] or [])

    last_harvest_sync = None
    ledger_path = base / "harvest_ledger.json"
    if ledger_path.exists():
        last_harvest_sync = datetime.fromtimestamp(
            ledger_path.stat().st_mtime, tz=timezone.utc).isoformat()

    health = build_health(
        events, ledger or {},
        stale_files=stale_files,
        raw_counts={
            "best_proof_files": len(best_files) if best_files is not None else None,
            "axle_entries": len(axle) if axle is not None else None,
            "submitted_night_targets": (len(submitted)
                                        if submitted is not None else None),
            "night_submit_log_lines": len(log_lines),
        },
        last_harvest_sync=last_harvest_sync)

    # Riemann: probed 2026-08-27 — no per-theorem dot-name table; NO network call.
    warnings.append(RIEMANN_WARNING)

    data = {
        "generated_at": generated_at,
        "funnel": funnel,
        "targets": rows,
        "yield_matrix": matrix,
        "health": health,
        "riemann": None,
        "warnings": warnings,
    }
    with open(out_path, "w") as fh:
        json.dump(data, fh, indent=1)
        fh.write("\n")

    if funnel:
        print("funnel:")
        for key, value in funnel.items():
            print("  %-18s %s" % (key, value))
    print("targets: %s" % (len(rows) if rows is not None else None))
    print("warnings: %d" % len(warnings))
    for warning in warnings:
        print("  ! %s" % warning[:160])
    print("wrote %s" % out_path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
