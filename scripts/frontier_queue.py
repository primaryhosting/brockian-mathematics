#!/usr/bin/env python3
"""Frontier Target Queue generator.

Merges seed sources into research/frontier_queue.json — the ranked,
append-only queue of proof targets. Spec:
docs/superpowers/specs/2026-08-27-frontier-target-queue-design.md

Truth rules: the registry is the only authority on PROVED; entries are never
deleted (stale, not gone); proved/refuted require evidence.attestation.

Scoring weights are EDITORIAL, not empirical (spec §4).
"""
import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

DEFAULT_PATHS = {
    "registry": os.path.join(REPO, "registry", "theorems.json"),
    "triage": os.path.join(REPO, "research", "frontier_triage.json"),
    "top100": os.path.join(REPO, "research", "top100-problems.json"),
    "wiedijk": os.path.join(REPO, "research", "wiedijk100.json"),
    "manual": os.path.join(REPO, "research", "manual-targets.json"),
    "mined": os.path.join(REPO, "research", "mined-targets.json"),
    "queue": os.path.join(REPO, "research", "frontier_queue.json"),
}

LEGIBILITY = {"wiedijk-gap": 5, "targets-board": 4, "registry-conjecture": 3,
              "manual": 3, "frontier_triage": 2, "miner": 2}
STATUSES = {"open", "assigned", "in_progress", "proved", "refuted", "stale"}


class QueueIntegrityError(Exception):
    pass


def _norm(text):
    return re.sub(r"\s+", " ", (text or "").strip().lower())


def _mk_id(key):
    return "ftq-" + hashlib.sha1(key.encode()).hexdigest()[:12]


def _entry(key, statement, lean_target, source, tractability, novelty=3):
    return {
        "id": _mk_id(key),
        "statement": statement,
        "lean_target": lean_target,
        "source": source,
        "scores": {"legibility": LEGIBILITY[source],
                   "tractability": tractability, "novelty": novelty},
    }


def _load(path, default=None):
    if not os.path.exists(path):
        return default
    with open(path) as f:
        return json.load(f)


def collect(paths):
    """Yield candidate entries from every present source. Dedup key priority:
    lean name when the target exists in the corpus, else normalized statement."""
    out = {}

    def add(key, cand):
        # highest-legibility source keeps the entry body, but scores merge
        # UPWARD across sources — a registry conjecture that triage marks GO
        # must keep tractability 5 (spec §4), not the registry default.
        if not key:
            return
        cand = dict(cand)
        cand["id"] = _mk_id(key)
        old = out.get(key)
        if old is None:
            out[key] = cand
            return
        keep = old if LEGIBILITY[old["source"]] >= LEGIBILITY[cand["source"]] else cand
        keep = dict(keep)
        keep["scores"] = {
            "legibility": max(old["scores"]["legibility"], cand["scores"]["legibility"]),
            "tractability": max(old["scores"]["tractability"], cand["scores"]["tractability"]),
            "novelty": max(old["scores"]["novelty"], cand["scores"]["novelty"]),
        }
        out[key] = keep

    registry = _load(paths["registry"]) or {"theorems": []}
    for t in registry["theorems"]:
        if t.get("register") not in ("CONJECTURE", "CONDITIONAL"):
            continue
        tract = 3 if t.get("register") == "CONJECTURE" else 2
        add(t["name"], _entry(
            t["name"], t.get("statement") or t["name"],
            {"kind": "existing-conjecture", "name": t["name"],
             "module": t.get("module", "")},
            "registry-conjecture", tract))

    triage = _load(paths["triage"])
    if triage:
        for t in triage.get("targets", []):
            tract = 5 if str(t.get("recommendation", "")).lower().startswith("go") else 3
            add(t["name"], _entry(
                t["name"], t.get("statement") or t["name"],
                {"kind": "existing-conjecture", "name": t["name"],
                 "module": t.get("module", "")},
                "frontier_triage", tract))
    else:
        print("WARN: triage source missing — skipped", file=sys.stderr)

    top100 = _load(paths["top100"])
    if top100:
        problems = top100 if isinstance(top100, list) else top100.get("problems", [])
        for p in problems:
            if str(p.get("status", "")).lower() != "open":
                continue
            formal = p.get("brockian")
            title = p.get("name") or ""
            stmt = p.get("statement") or title
            add(_norm(title), _entry(
                _norm(title), ("%s: %s" % (title, stmt)) if stmt != title else title,
                ({"kind": "statement-skeleton", "module": formal} if formal
                 else {"kind": "unformalized"}),
                "targets-board", 3 if formal else 1))
    else:
        print("WARN: top100 source missing — skipped", file=sys.stderr)

    wiedijk = _load(paths["wiedijk"])
    if wiedijk:
        if isinstance(wiedijk, dict):
            wiedijk = wiedijk.get("theorems", [])
        for w in wiedijk:
            if w.get("corpus_match"):
                continue  # already formalized here → not a gap
            add(_norm(w["title"]), _entry(
                _norm(w["title"]), w["title"],
                {"kind": "unformalized", "wiedijk_index": w["index"]},
                "wiedijk-gap", 1))
    else:
        print("WARN: wiedijk source missing — skipped", file=sys.stderr)

    manual = _load(paths["manual"])
    if manual:
        for m in manual.get("targets", []):
            add(m["slug"], _entry(
                m["slug"], m["statement"], dict(m.get("lean_target", {})),
                "manual", 4))

    mined = _load(paths.get("mined", ""))
    if mined:
        for m in mined.get("targets", []):
            # miner candidates carry their own tractability (1-5) from the
            # verification pass; default conservative 2
            add(m["slug"], _entry(
                m["slug"], m["statement"], dict(m.get("lean_target", {})),
                "miner", int(m.get("tractability", 2))))
    return out


def generate(paths, now, commit):
    prev = _load(paths["queue"], {"entries": []})
    prev_by_id = {e["id"]: e for e in prev["entries"]}

    # integrity check on the inherited file
    for e in prev["entries"]:
        if e.get("status") in ("proved", "refuted") and not e.get("evidence", {}).get("attestation"):
            raise QueueIntegrityError(
                "entry %s is %s without evidence.attestation" % (e["id"], e["status"]))
        if e.get("status") not in STATUSES:
            raise QueueIntegrityError("entry %s has illegal status %r" % (e["id"], e.get("status")))

    fresh = collect(paths)
    fresh_ids = {c["id"] for c in fresh.values()}

    registry = _load(paths["registry"]) or {"theorems": []}
    reg_by_name = {t["name"]: t for t in registry["theorems"]}

    entries = []
    for cand in fresh.values():
        old = prev_by_id.get(cand["id"])
        if old:
            e = dict(old)
            e["scores"] = cand["scores"]  # scores/ranks refresh; status/history persist
            e["statement"] = cand["statement"]
            e["lean_target"] = cand["lean_target"]
            e["source"] = cand["source"]
            if e["status"] == "stale":
                e["status"] = "open"
                e["history"] = e["history"] + [
                    {"at": now, "event": "reopened", "by": "generator"}]
        else:
            e = dict(cand)
            e.update({"status": "open", "assigned_engine": None,
                      "evidence": {"attestation": "", "links": []},
                      "history": [{"at": now, "event": "created", "by": "generator"}]})
        entries.append(e)

    # carry forward entries dropped by every source → stale
    for old_id, old in prev_by_id.items():
        if old_id in fresh_ids:
            continue
        e = dict(old)
        if e["status"] not in ("stale", "proved", "refuted"):
            e["status"] = "stale"
            e["history"] = e["history"] + [
                {"at": now, "event": "stale", "by": "generator"}]
        entries.append(e)

    # registry reconciliation — the registry is the authority
    for e in entries:
        name = e["lean_target"].get("name")
        reg = reg_by_name.get(name) if name else None
        if reg and reg.get("register") == "PROVED" and e["status"] != "proved":
            e["status"] = "proved"
            e["evidence"] = {"attestation": name, "links": []}
            e["history"] = e["history"] + [
                {"at": now, "event": "proved (registry reconciliation)",
                 "by": "generator:registry"}]

    def score(e):
        s = e["scores"]
        return 3 * s["legibility"] + 2 * s["tractability"] + s["novelty"]

    entries.sort(key=lambda e: (-score(e), e["id"]))
    for i, e in enumerate(entries):
        e["rank"] = i + 1

    return {"version": 1, "generated_at": now, "generator_commit": commit,
            "entries": entries}


def render_review(queue, limit=60):
    lines = ["# Frontier Queue — review rendering",
             "", "Generated %s · commit %s · %d entries" % (
                 queue["generated_at"], queue["generator_commit"], len(queue["entries"])),
             "", "| rank | id | status | source | L/T/N | statement |",
             "|---|---|---|---|---|---|"]
    for e in queue["entries"][:limit]:
        s = e["scores"]
        stmt = (e["statement"][:90] + "…") if len(e["statement"]) > 90 else e["statement"]
        stmt = stmt.replace("|", "\\|").replace("\n", " ")
        lines.append("| %d | %s | %s | %s | %d/%d/%d | %s |" % (
            e["rank"], e["id"], e["status"], e["source"],
            s["legibility"], s["tractability"], s["novelty"], stmt))
    if len(queue["entries"]) > limit:
        lines.append("")
        lines.append("… %d more entries in frontier_queue.json" % (len(queue["entries"]) - limit))
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--now", default=None, help="ISO timestamp override (tests)")
    ap.add_argument("--review", action="store_true", help="also write REVIEW.md")
    args = ap.parse_args()
    now = args.now
    if not now:
        import datetime
        now = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    try:
        commit = subprocess.check_output(
            ["git", "rev-parse", "--short", "HEAD"], cwd=REPO).decode().strip()
    except Exception:
        commit = "unknown"
    queue = generate(DEFAULT_PATHS, now=now, commit=commit)
    with open(DEFAULT_PATHS["queue"], "w") as f:
        json.dump(queue, f, indent=1, ensure_ascii=False)
        f.write("\n")
    print("wrote %s (%d entries)" % (DEFAULT_PATHS["queue"], len(queue["entries"])))
    if args.review:
        path = os.path.join(REPO, "research", "frontier_queue.REVIEW.md")
        with open(path, "w") as f:
            f.write(render_review(queue))
        print("wrote", path)


if __name__ == "__main__":
    main()
