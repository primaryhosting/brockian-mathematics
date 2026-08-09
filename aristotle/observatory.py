#!/usr/bin/env python3
"""observatory.py — one-glance status of the whole proof fleet across all pipelines.
Aggregates the ledgers (submit / harvest / verify / best / domain catalogue) into a
JSON + markdown summary. Read-only."""
import collections
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parent
REPO = ROOT.parent


def load(p, d):
    p = ROOT / p if not str(p).startswith("/") else pathlib.Path(p)
    try:
        return json.loads(p.read_text())
    except Exception:  # noqa: BLE001
        return d


def main():
    night = load("submitted_night.json", {})
    harvest = load("harvest_ledger.json", {})
    vstate = load("harvest_100/verify_state.json", {})
    best = load("best_proofs/manifest.json", {})
    domains = load(REPO / "registry" / "domains.json", {})

    submits = sum(len(v.get("ids", [])) for v in night.values())
    sub_by_acct = collections.Counter()
    sub_by_dom = collections.Counter()
    for t, v in night.items():
        for i in v.get("ids", []):
            sub_by_acct[i["account"]] += 1
        dom = v.get("tier", "?").split("-")[-1]
        sub_by_dom[dom] += len(v.get("ids", []))
    proved = sum(1 for v in harvest.values() if v.get("verdict") == "PROVED")
    stopped = sum(1 for v in harvest.values() if v.get("verdict") == "STOPPED")
    verified = sum(1 for s in vstate.values() if s.get("compiles") is True)

    summary = {
        "submitted_jobs": submits, "by_account": dict(sub_by_acct), "by_domain": dict(sub_by_dom),
        "unique_targets_attempted": len(night),
        "harvested": len(harvest), "proved": proved, "stopped": stopped,
        "lake_verified": verified, "best_proofs_selected": len(best),
        "domain_catalogue": len(domains),
    }
    (ROOT / "observatory.json").write_text(json.dumps(summary, indent=1))
    lines = ["# Proof-fleet observatory", ""]
    for k, v in summary.items():
        lines.append(f"- **{k}**: {v}")
    (ROOT / "observatory.md").write_text("\n".join(lines))
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
