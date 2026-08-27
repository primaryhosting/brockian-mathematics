# Frontier Target Queue Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the ranked proof-target queue (`research/frontier_queue.json`) + generator + Supabase mirror per `docs/superpowers/specs/2026-08-27-frontier-target-queue-design.md`.

**Architecture:** Stdlib-only Python generator merges 5 seed sources → ranked, append-only queue JSON in the repo (truth); a sync script mirrors it to `atlas_frontier_queue` in Riemann Supabase (loud-BLOCKED if the service key 401s). Human review gate before any engine consumes it.

**Tech Stack:** Python 3 stdlib (`json`, `hashlib`, `unittest`, `urllib`), PostgREST upsert for Supabase. No new dependencies.

**Working directory:** `~/Projects/brockian-mathematics` (branch `conveyor/2026-08-18`; commit with `--no-verify`, explicit paths only — NEVER `git add -A`, the tree has ~18k unrelated uncommitted files).

**Environment facts the implementer must know:**
- `registry/theorems.json`: `{generated_from, summary, theorems:[...]}`, 12,377 entries. Entry fields used here: `name`, `kind`, `module`, `statement`, `register` (PROVED 11,646 / DEFINITION 651 / CONJECTURE 40 / CONDITIONAL 33 / DISCHARGED 7), `source.file`.
- `frontier_triage.json` (vendor from the AutoLab node tree — `autolab pull`/`clone` currently fail with a git protocol error, so copy from `/Users/acutis/.autolab/ACUTISs-Mac-mini.local/projects/primaryhosting--brockian-mathematics/nodes/brockian-mm/trees/831a203d/research/frontier_triage.json`): `{generated_by, frontier_targets_total, targets_recommended_go, rung_counts, targets:[...]}`, 60 targets; fields used: `name`, `register`, `module`, `statement`, `statement_found`, `recommendation` ("go" ×17 / "no-go" ×43).
- `research/manual-targets.json` already exists (3 targets; fields `slug`, `statement`, `lean_target.kind`, `lean_target.cluster`, `notes`).
- `research/top100-problems.json`: vendor via the claude.ai Lovable MCP — `read_file` on project `dd8308ac-0860-42ae-908c-41b306b58858`, path `src/data/top100-problems.json` (104 problems). If the fetch fails, SKIP this source (generator warns loudly on missing optional sources) and note it in the final report — do not block.
- Tests live in `tests/test_*.py`, plain `unittest`, run via `python3 -m unittest tests.test_frontier_queue -v`.
- Supabase env (after `source ~/.openclaw/load-vault.sh`): `RIEMANN_SUPABASE_URL`, `RIEMANN_SUPABASE_KEY` (may 401 — expected, spec'd as BLOCKED), `RIEMANN_SUPABASE_ANON_KEY`.

---

## Chunk 1: everything

### Task 1: Vendor the seed sources

**Files:**
- Create: `research/frontier_triage.json` (copy)
- Create: `research/wiedijk100.json` (curated)
- Create: `research/top100-problems.json` (vendored via Lovable MCP; skippable)

- [x] **Step 1: Copy the triage file from the node tree**

```bash
cp /Users/acutis/.autolab/ACUTISs-Mac-mini.local/projects/primaryhosting--brockian-mathematics/nodes/brockian-mm/trees/831a203d/research/frontier_triage.json \
   ~/Projects/brockian-mathematics/research/frontier_triage.json
python3 -c "import json; t=json.load(open('/Users/acutis/Projects/brockian-mathematics/research/frontier_triage.json')); print(len(t['targets']), 'targets')"
```
Expected: `60 targets`

- [x] **Step 2: Vendor top100-problems.json via Lovable MCP** *(vendored ahead of this run; real fields are `name`/`statement`/`status`(open|resolved|disputed|independent)/`brockian` — generator top100 block adjusted accordingly)*

Use `mcp__claude_ai_Lovable__read_file` with `project_id: dd8308ac-0860-42ae-908c-41b306b58858`, `path: src/data/top100-problems.json`; write the content to `research/top100-problems.json`. Verify the shape AND that titles are usable: `python3 -c "import json; d=json.load(open('research/top100-problems.json')); items=d if isinstance(d,list) else d.get('problems',[]); titles=[(p.get('name') or p.get('title') or '') for p in items]; assert len(items)>=100 and all(titles) and len(set(titles))==len(titles), (len(items), titles[:3]); print('OK', len(items))"`. If the real field names differ from `name`/`title`/`status`/`formalized_module`, adjust the generator's top100 block (Task 3) to the actual fields — the plan's names are guesses about unvendored data. If the MCP read fails after 2 attempts, skip (source is optional) and record the skip.

- [x] **Step 3: Create `research/wiedijk100.json`** *(4 corpus matches: #45 Partition→euler_odd_eq_distinct, #51 Wilson→prime_iff_dvd_factorial_succ, #88 Derangements→derangement_closed, #98 Bertrand→bertrand_holds. Note: canonical #86 is "Lebesgue Measure and Integration" — the Pentagonal Number Theorem is not on Wiedijk's list, so `pentagonalNumberTheorem` has no wiedijk match.)*

Curate the standard Wiedijk "Formalizing 100 Theorems" list as `{"provenance": "Freek Wiedijk, 'Formalizing 100 Theorems' (cs.ru.nl/~freek/100), curated from model knowledge 2026-08-27 — titles unvalidated by test", "theorems": [...]}` where each theorem is `{"index": 1..100, "title": "...", "corpus_match": "<registry name or null>"}`. (The generator reads the `theorems` key when the file is a dict, or the bare array.) Populate `corpus_match` by scanning `registry/theorems.json` names case-insensitively for obvious matches (e.g. `pentagonalNumberTheorem` → #86 "Pentagonal Number Theorem"; check also: FTA, irrationality of √2, e; IVT; Ramsey; Cayley–Hamilton). Be conservative: match only when the registry name unambiguously names the theorem; otherwise `null`. Verify: `python3 -c "import json; w=json.load(open('research/wiedijk100.json')); print(len(w), sum(1 for e in w if e['corpus_match']))"` → `100 <n>` with n small (likely 1–10).

- [x] **Step 4: Commit**

```bash
cd ~/Projects/brockian-mathematics && git add research/frontier_triage.json research/wiedijk100.json && \
  { [ -f research/top100-problems.json ] && git add research/top100-problems.json || true; } && \
  git commit --no-verify -m "research: vendor frontier-queue seed sources (triage from AutoLab, wiedijk100, top100 board)"
```

### Task 2: Generator — failing tests first

**Files:**
- Create: `tests/test_frontier_queue.py`
- Create: `scripts/frontier_queue.py` (Task 3)

- [ ] **Step 1: Write the failing tests**

```python
"""Tests for scripts/frontier_queue.py — the Frontier Target Queue generator.

Spec: docs/superpowers/specs/2026-08-27-frontier-target-queue-design.md
"""
import json
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
import frontier_queue as fq

NOW = "2026-08-27T12:00:00Z"


def mini_sources(tmp):
    """Write a minimal fixture of every source into tmp; return paths dict."""
    reg = {"theorems": [
        {"name": "Brockian.X.conj_one", "kind": "conjecture", "module": "Brockian.X",
         "statement": "conjecture one", "register": "CONJECTURE", "source": {"file": "Brockian/X.lean"}},
        {"name": "Brockian.X.proved_one", "kind": "theorem", "module": "Brockian.X",
         "statement": "", "register": "PROVED", "source": {"file": "Brockian/X.lean"}},
    ]}
    triage = {"targets": [
        {"name": "Brockian.X.conj_one", "register": "CONJECTURE", "module": "Brockian.X",
         "statement": "conjecture one", "statement_found": True, "recommendation": "go"},
        {"name": "Brockian.Y.cond_two", "register": "CONDITIONAL", "module": "Brockian.Y",
         "statement": "cond two", "statement_found": True, "recommendation": "no-go"},
    ]}
    wiedijk = [{"index": 1, "title": "Irrationality of sqrt 2", "corpus_match": None}]
    manual = {"targets": [
        {"slug": "manual-a", "statement": "manual statement a",
         "lean_target": {"kind": "statement-skeleton", "cluster": "C"}, "notes": ""}]}
    paths = {}
    for key, obj in [("registry", reg), ("triage", triage), ("wiedijk", wiedijk),
                     ("manual", manual)]:
        p = os.path.join(tmp, key + ".json")
        with open(p, "w") as f:
            json.dump(obj, f)
        paths[key] = p
    paths["top100"] = os.path.join(tmp, "missing-top100.json")  # absent, optional
    paths["queue"] = os.path.join(tmp, "frontier_queue.json")
    return paths


class TestGenerator(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.paths = mini_sources(self.tmp)

    def gen(self):
        return fq.generate(self.paths, now=NOW, commit="testsha")

    def test_stable_ids_and_dedup_across_sources(self):
        q = self.gen()
        ids = [e["id"] for e in q["entries"]]
        self.assertEqual(len(ids), len(set(ids)))
        # conj_one appears in registry AND triage -> one entry, keyed by name
        matches = [e for e in q["entries"]
                   if e["lean_target"].get("name") == "Brockian.X.conj_one"]
        self.assertEqual(len(matches), 1)
        # regen mints identical ids
        q2 = fq.generate(self.paths, now=NOW, commit="testsha")
        self.assertEqual(ids, [e["id"] for e in q2["entries"]])

    def test_ranking_deterministic_and_ordered(self):
        q = self.gen()
        ranks = [e["rank"] for e in q["entries"]]
        self.assertEqual(ranks, list(range(1, len(ranks) + 1)))
        scores = [3 * e["scores"]["legibility"] + 2 * e["scores"]["tractability"]
                  + e["scores"]["novelty"] for e in q["entries"]]
        self.assertEqual(scores, sorted(scores, reverse=True))

    def test_regen_preserves_status_and_history(self):
        q = self.gen()
        target = q["entries"][0]
        target["status"] = "assigned"
        target["assigned_engine"] = "autolab-brockian"
        target["history"].append({"at": NOW, "event": "assigned", "by": "test"})
        with open(self.paths["queue"], "w") as f:
            json.dump(q, f)
        q2 = self.gen()
        e2 = next(e for e in q2["entries"] if e["id"] == target["id"])
        self.assertEqual(e2["status"], "assigned")
        self.assertEqual(len(e2["history"]), 2)  # created + assigned

    def test_dropped_entry_goes_stale_and_returns_open(self):
        q = self.gen()
        with open(self.paths["queue"], "w") as f:
            json.dump(q, f)
        manual_id = next(e["id"] for e in q["entries"] if e["source"] == "manual")
        # drop the manual source entirely
        with open(self.paths["manual"], "w") as f:
            json.dump({"targets": []}, f)
        q2 = self.gen()
        e2 = next(e for e in q2["entries"] if e["id"] == manual_id)
        self.assertEqual(e2["status"], "stale")
        # re-list it
        with open(self.paths["manual"], "w") as f:
            json.dump({"targets": [{"slug": "manual-a", "statement": "manual statement a",
                                    "lean_target": {"kind": "statement-skeleton", "cluster": "C"},
                                    "notes": ""}]}, f)
        with open(self.paths["queue"], "w") as f:
            json.dump(q2, f)
        q3 = self.gen()
        e3 = next(e for e in q3["entries"] if e["id"] == manual_id)
        self.assertEqual(e3["status"], "open")
        events = [h["event"] for h in e3["history"]]
        self.assertIn("stale", events)
        self.assertIn("reopened", events)

    def test_registry_reconciliation_flips_proved(self):
        q = self.gen()
        with open(self.paths["queue"], "w") as f:
            json.dump(q, f)
        reg = json.load(open(self.paths["registry"]))
        for t in reg["theorems"]:
            if t["name"] == "Brockian.X.conj_one":
                t["register"] = "PROVED"
        with open(self.paths["registry"], "w") as f:
            json.dump(reg, f)
        q2 = self.gen()
        e2 = next(e for e in q2["entries"]
                  if e["lean_target"].get("name") == "Brockian.X.conj_one")
        self.assertEqual(e2["status"], "proved")
        self.assertEqual(e2["evidence"]["attestation"], "Brockian.X.conj_one")
        self.assertTrue(any(h["by"] == "generator:registry" for h in e2["history"]))

    def test_proved_without_attestation_refused(self):
        q = self.gen()
        q["entries"][0]["status"] = "proved"
        q["entries"][0]["evidence"] = {"attestation": "", "links": []}
        with open(self.paths["queue"], "w") as f:
            json.dump(q, f)
        with self.assertRaises(fq.QueueIntegrityError):
            self.gen()

    def test_dedup_merges_tractability_upward(self):
        # conj_one is a registry conjecture (legibility 3, tract 3) AND a
        # triage GO target (legibility 2, tract 5): body from registry,
        # tractability merged up to 5. Guards the spec §4 GO=5 rule.
        q = self.gen()
        e = next(e for e in q["entries"]
                 if e["lean_target"].get("name") == "Brockian.X.conj_one")
        self.assertEqual(e["source"], "registry-conjecture")
        self.assertEqual(e["scores"]["tractability"], 5)

    def test_generation_byte_stable(self):
        a = json.dumps(self.gen(), sort_keys=True)
        b = json.dumps(self.gen(), sort_keys=True)
        self.assertEqual(a, b)


class TestSync(unittest.TestCase):
    def setUp(self):
        import frontier_queue_sync as fqs
        self.fqs = fqs
        self.tmp = tempfile.mkdtemp()
        self.queue_path = os.path.join(self.tmp, "frontier_queue.json")
        queue = {"generated_at": NOW, "entries": [{
            "id": "ftq-abc", "statement": "s", "lean_target": {}, "source": "manual",
            "scores": {"legibility": 3, "tractability": 4, "novelty": 3},
            "rank": 1, "status": "open", "assigned_engine": None,
            "evidence": {"attestation": "", "links": []}, "history": []}]}
        with open(self.queue_path, "w") as f:
            json.dump(queue, f)

    def test_dry_run_payload_matches_file(self):
        code = self.fqs.run(dry=True, env={}, queue_path=self.queue_path)
        self.assertEqual(code, 0)
        rows = self.fqs.rows(json.load(open(self.queue_path)))
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["id"], "ftq-abc")
        self.assertEqual(rows[0]["generated_at"], NOW)

    def test_blocked_without_service_key(self):
        code = self.fqs.run(dry=False, env={}, queue_path=self.queue_path)
        self.assertEqual(code, 2)  # BLOCKED, per spec §5


if __name__ == "__main__":
    unittest.main()
```

- [ ] **Step 2: Run tests, verify they fail on import**

```bash
cd ~/Projects/brockian-mathematics && python3 -m unittest tests.test_frontier_queue -v 2>&1 | tail -3
```
Expected: `ModuleNotFoundError: No module named 'frontier_queue'`

- [ ] **Step 3: Commit the failing tests**

```bash
git add tests/test_frontier_queue.py && git commit --no-verify -m "test: frontier queue generator (failing — TDD)"
```

### Task 3: Generator implementation

**Files:**
- Create: `scripts/frontier_queue.py`

- [ ] **Step 1: Implement**

```python
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
    "queue": os.path.join(REPO, "research", "frontier_queue.json"),
}

LEGIBILITY = {"wiedijk-gap": 5, "targets-board": 4, "registry-conjecture": 3,
              "manual": 3, "frontier_triage": 2}
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
            if str(p.get("status", "")).lower() in ("resolved", "resolved-by-others"):
                continue
            formal = p.get("formalized_module") or p.get("module")
            title = p.get("name") or p.get("title") or ""
            add(_norm(title), _entry(
                _norm(title), title,
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
```

- [ ] **Step 2: Run the tests**

```bash
cd ~/Projects/brockian-mathematics && python3 -m unittest tests.test_frontier_queue -v 2>&1 | tail -8
```
Expected: the 8 generator tests pass; the 2 `TestSync` tests still ERROR (`frontier_queue_sync` not yet written — it lands in Task 5). After Task 5, all 10 pass.

- [ ] **Step 3: Commit**

```bash
git add scripts/frontier_queue.py && git commit --no-verify -m "feat: frontier queue generator (merge 5 sources, rank, append-only, registry reconciliation)"
```

### Task 4: Generate queue v1 + review rendering

- [ ] **Step 1: Run the generator against the real sources**

```bash
cd ~/Projects/brockian-mathematics && python3 scripts/frontier_queue.py --review
```
Expected: `wrote research/frontier_queue.json (<n> entries)` with n ≈ 150–250 (40 CONJ + 33 COND + up to 60 triage-deduped + top100 opens + wiedijk gaps + 3 manual, minus dedup overlap), and `frontier_queue.REVIEW.md`.

- [ ] **Step 2: Sanity-check the output**

```bash
python3 - <<'EOF'
import json, collections
q = json.load(open('/Users/acutis/Projects/brockian-mathematics/research/frontier_queue.json'))
print(len(q['entries']), 'entries')
print(collections.Counter(e['source'] for e in q['entries']))
print(collections.Counter(e['status'] for e in q['entries']))
print('top 5:', [(e['rank'], e['source'], e['statement'][:40]) for e in q['entries'][:5]])
EOF
```
Expected: statuses all `open` (first generation — unless registry reconciliation legitimately proves something), triage go-targets and manual/wiedijk entries near the top.

- [ ] **Step 3: Commit**

```bash
git add research/frontier_queue.json research/frontier_queue.REVIEW.md && git commit --no-verify -m "feat: frontier queue v1 (first generated queue + review rendering)"
```

### Task 5: Supabase mirror (DDL + sync, loud-BLOCKED path)

**Files:**
- Create: `deploy/atlas_frontier_queue.sql`
- Create: `scripts/frontier_queue_sync.py`

- [ ] **Step 1: Write the DDL**

```sql
-- atlas_frontier_queue: read mirror of research/frontier_queue.json
-- (truth lives in git; this table is display-only. Spec 2026-08-27.)
create table if not exists atlas_frontier_queue (
  id text primary key,
  statement text not null,
  lean_target jsonb not null default '{}',
  source text not null,
  scores jsonb not null default '{}',
  rank integer not null,
  status text not null,
  assigned_engine text,
  evidence jsonb not null default '{}',
  history jsonb not null default '[]',
  generated_at timestamptz,
  synced_at timestamptz not null default now()
);
alter table atlas_frontier_queue enable row level security;
drop policy if exists "anon read frontier queue" on atlas_frontier_queue;
create policy "anon read frontier queue" on atlas_frontier_queue
  for select to anon using (true);
grant select on atlas_frontier_queue to anon;
```

- [ ] **Step 2: Apply the DDL** via the claude.ai Lovable MCP `query_database` on project `dd8308ac-0860-42ae-908c-41b306b58858` (the Riemann Lab project owns this Supabase). If that project has no database access, record BLOCKED and continue — the sync script's 401 path covers it.

- [ ] **Step 3: Write the sync script**

```python
#!/usr/bin/env python3
"""Mirror research/frontier_queue.json to Riemann Supabase (display only).

Exit codes: 0 synced · 2 BLOCKED (missing/401 service key) · 1 other error.
--dry-run prints the payload row count + first row and writes nothing.
"""
import json
import os
import sys
import urllib.error
import urllib.request

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
QUEUE = os.path.join(REPO, "research", "frontier_queue.json")


def rows(queue):
    return [{
        "id": e["id"], "statement": e["statement"],
        "lean_target": e["lean_target"], "source": e["source"],
        "scores": e["scores"], "rank": e["rank"], "status": e["status"],
        "assigned_engine": e.get("assigned_engine"),
        "evidence": e.get("evidence", {}), "history": e.get("history", []),
        "generated_at": queue["generated_at"],
    } for e in queue["entries"]]


def run(dry, env, queue_path=QUEUE):
    queue = json.load(open(queue_path))
    payload = rows(queue)
    if dry:
        print("dry-run: %d rows; first=%s" % (len(payload),
              json.dumps(payload[0])[:160]))
        return 0
    url = env.get("RIEMANN_SUPABASE_URL", "").rstrip("/")
    key = env.get("RIEMANN_SUPABASE_SERVICE_KEY") or env.get("RIEMANN_SUPABASE_KEY")
    if not url or not key:
        print("BLOCKED: service key — RIEMANN_SUPABASE_URL/SERVICE_KEY unset")
        return 2
    req = urllib.request.Request(
        url + "/rest/v1/atlas_frontier_queue?on_conflict=id",
        data=json.dumps(payload).encode(),
        headers={"apikey": key, "Authorization": "Bearer " + key,
                 "Content-Type": "application/json",
                 "Prefer": "resolution=merge-duplicates"},
        method="POST")
    try:
        with urllib.request.urlopen(req) as r:
            print("synced %d rows (HTTP %d)" % (len(payload), r.status))
            return 0
    except urllib.error.HTTPError as err:
        if err.code in (401, 403):
            print("BLOCKED: service key — HTTP %d from PostgREST "
                  "(mint a real service key; known blocker)" % err.code)
            return 2
        print("ERROR: HTTP %d — %s" % (err.code, err.read()[:300]))
        return 1
    except urllib.error.URLError as err:
        print("ERROR: connection failed — %s" % err.reason)
        return 1


def main():
    return run(dry="--dry-run" in sys.argv, env=dict(os.environ))


if __name__ == "__main__":
    sys.exit(main())
```

- [ ] **Step 4: Test the dry run + real run**

```bash
cd ~/Projects/brockian-mathematics && python3 -m unittest tests.test_frontier_queue -v 2>&1 | tail -4
python3 scripts/frontier_queue_sync.py --dry-run
source ~/.openclaw/load-vault.sh 2>/dev/null; python3 scripts/frontier_queue_sync.py; echo "exit=$?"
```
Expected: all 10 unit tests pass; dry-run prints the row count; real run prints either `synced N rows` or `BLOCKED: service key` with exit 2 (both acceptable per spec — record which).

- [ ] **Step 5: Commit**

```bash
git add deploy/atlas_frontier_queue.sql scripts/frontier_queue_sync.py && git commit --no-verify -m "feat: frontier queue Supabase mirror (DDL + sync, loud-BLOCKED on missing service key)"
```

### Task 6: Queue README (lifecycle + engine rules)

**Files:**
- Create: `research/frontier_queue.README.md`

- [ ] **Step 1: Write it** — must cover: schema summary; the legal transition table (`open → assigned → in_progress → proved | refuted`; any → `stale` on source-drop **except `proved`/`refuted`, which never go stale — the generator preserves settled outcomes; this is a documented refinement of the spec's table**; `stale → open` on re-list); engine rules (engines flip statuses by editing the file in normal experiment commits, history entry names the experiment id; `proved`/`refuted` REQUIRE `evidence.attestation`; the registry is the only authority); the two-repo manual sync step (AutoLab main → GitHub via workspace pull or node-tree copy); regen (`python3 scripts/frontier_queue.py --review`) and sync commands; the HARD GATE — no engine consumes the queue until Chris reviews `frontier_queue.REVIEW.md` and says go.

- [ ] **Step 2: Commit**

```bash
git add research/frontier_queue.README.md && git commit --no-verify -m "docs: frontier queue README (lifecycle, engine rules, sync, review gate)"
```

### Task 7 (separable — failure must not block Tasks 1–6): Zumkeller sync-back

- [ ] **Step 1: Locate the wave-17 registrations** in the AutoLab node tree (`~/.autolab/ACUTISs-Mac-mini.local/projects/primaryhosting--brockian-mathematics/nodes/brockian-mm/trees/`, newest tree; or `repo.git` main). Find: the 4 Zumkeller theorem names newly `PROVED` in that tree's `registry/theorems.json` relative to the local repo's, and the Lean source they were verified from.

- [ ] **Step 2: Port via the normal registry path** — copy the proof content into the appropriate `Brockian/` module following how the wave did it, then regenerate/patch the registry the same way the repo's tooling does (`scripts/gen_registry.py` or the registration path the agent used — inspect `scripts/autolab_wave16.py` in the tree for the exact calls). Do NOT hand-edit registry entries without AXLE verification metadata; re-run AXLE via `scripts/axle_client.py` (needs `AXLE_API_KEY` from vault) if the tooling requires fresh attestation.

- [ ] **Step 3: Verify** — `python3 scripts/audit_registry_consistency.py` (or the repo's registry consistency test in `tests/`) passes; the 4 names show `register: PROVED` with AXLE verdicts. Then regen the queue (`python3 scripts/frontier_queue.py --review`) — reconciliation should flip any queued Zumkeller targets to `proved`.

- [ ] **Step 4: Commit** (explicit paths: the Lean file(s) + `registry/theorems.json` + regenerated queue files). If any step proves to require a full lake build or missing tooling, STOP, leave the tree clean, and report the blocker instead of forcing it.

### Task 8: Final verification

- [ ] Run the full new test file + the repo's registry-consistency tests; verify idempotence with a pinned timestamp: run `python3 scripts/frontier_queue.py --now 2026-08-27T00:00:00Z --review` twice and `git diff --stat research/frontier_queue.json` between runs — must be empty (`--now` pins `generated_at`, which otherwise differs every run). Then run once WITHOUT `--now` to stamp the real generation time as the committed version. Report: entry count by source/status, top-10 ranked, sync status (synced/BLOCKED), Zumkeller outcome, and hand `research/frontier_queue.REVIEW.md` to Chris for the review gate.
