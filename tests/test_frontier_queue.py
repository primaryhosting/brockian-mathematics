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


class TestMinerSource(unittest.TestCase):
    def test_miner_entries_collected_with_own_tractability(self):
        tmp = tempfile.mkdtemp()
        paths = mini_sources(tmp)
        paths["mined"] = os.path.join(tmp, "mined.json")
        with open(paths["mined"], "w") as f:
            json.dump({"targets": [{"slug": "mined-a", "statement": "mined statement a",
                                    "lean_target": {"kind": "statement-skeleton", "cluster": "X"},
                                    "tractability": 4}]}, f)
        q = fq.generate(paths, now=NOW, commit="testsha")
        e = next(e for e in q["entries"] if e["source"] == "miner")
        self.assertEqual(e["scores"]["legibility"], 2)
        self.assertEqual(e["scores"]["tractability"], 4)
