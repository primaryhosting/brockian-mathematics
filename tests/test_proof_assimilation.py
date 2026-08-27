import json
import os
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "scripts"))
import proof_assimilation as pa


NOW = "2026-08-27T17:00:00Z"


def fixture():
    ledger = {
        "p-short": {"target": "Brockian.Foundation.core", "account": "admin", "verdict": "PROVED"},
        "p-clean": {"target": "Brockian.Foundation.core", "account": "chris", "verdict": "PROVED"},
        "p-stop": {"target": "Brockian.Foundation.core", "account": "admin", "verdict": "STOPPED"},
        "p-other": {"target": "Brockian.Other.goal", "account": "admin", "verdict": "PROVED"},
    }
    best = {
        "Brockian.Foundation.core": {
            "project_id": "p-clean", "chosen": "chris_p-clean.lean", "lines": 40,
            "compiles": True, "n_candidates": 3,
        },
        "Brockian.Other.goal": {
            "project_id": "p-other", "chosen": "admin_p-other.lean", "lines": 20,
            "compiles": None, "n_candidates": 1,
        },
    }
    axle = {
        "Brockian_Foundation_core.lean": {"verified": True, "hash": "a"},
        "Brockian_Other_goal.lean": {"verified": True, "hash": "b"},
    }
    axioms = {
        "Brockian_Foundation_core.lean": {
            "trusted": True, "axioms": ["propext", "Classical.choice"], "hash": "a",
        },
        "Brockian_Other_goal.lean": {"trusted": True, "axioms": [], "hash": "b"},
    }
    registry = {"theorems": [
        {"name": "Brockian.Dependency.done", "register": "PROVED"},
        {"name": "Brockian.Already.done", "register": "PROVED"},
    ]}
    frontier = {"entries": [
        {
            "id": "foundation", "statement": "core", "status": "open",
            "lean_target": {"name": "Brockian.Foundation.core"},
            "scores": {"legibility": 3, "tractability": 4, "novelty": 3},
            "target_class": "foundation", "unlocks": ["a", "b", "c"],
            "consumers": ["x", "y"], "depends_on": ["Brockian.Dependency.done"],
        },
        {
            "id": "other", "statement": "other", "status": "open",
            "lean_target": {"name": "Brockian.Other.goal"},
            "scores": {"legibility": 5, "tractability": 5, "novelty": 5},
            "depends_on": ["Brockian.Missing.dep"],
        },
        {
            "id": "done", "statement": "done", "status": "open",
            "lean_target": {"name": "Brockian.Already.done"},
            "scores": {"legibility": 5, "tractability": 5, "novelty": 5},
        },
    ]}
    return ledger, best, axle, axioms, registry, frontier


class TestAssimilation(unittest.TestCase):
    def report(self):
        ledger, best, axle, axioms, registry, frontier = fixture()
        return pa.build_report(
            ledger=ledger, best=best, axle=axle, axioms=axioms,
            registry=registry, frontier=frontier, now=NOW,
        )

    def test_four_gate_promotion_is_fail_closed(self):
        report = self.report()
        foundation = next(g for g in report["proof_groups"] if g["target"] == "Brockian.Foundation.core")
        other = next(g for g in report["proof_groups"] if g["target"] == "Brockian.Other.goal")
        self.assertEqual(foundation["winner_gate"], "promotion_ready")
        self.assertEqual(foundation["next_action"], "promote")
        self.assertEqual(other["winner_gate"], "attested_pending_local")
        self.assertEqual(other["next_action"], "local_verify")

    def test_attempts_are_compared_and_rejections_retained(self):
        report = self.report()
        foundation = next(g for g in report["proof_groups"] if g["target"] == "Brockian.Foundation.core")
        self.assertEqual(foundation["attempt_count"], 3)
        self.assertEqual(foundation["winner_project_id"], "p-clean")
        self.assertEqual(sum(a["gate"] == "rejected" for a in foundation["attempts"]), 1)
        self.assertEqual(report["summary"]["duplicate_attempts"], 2)

    def test_compounding_value_beats_raw_editorial_score(self):
        report = self.report()
        self.assertEqual(report["steering_queue"][0]["target"], "Brockian.Foundation.core")
        row = report["steering_queue"][0]
        self.assertEqual(row["unlocks"], 3)
        self.assertEqual(row["recommended_action"], "promote")
        self.assertNotIn("Brockian.Already.done", [r["target"] for r in report["steering_queue"]])

    def test_disagreement_blocks_winner(self):
        ledger, best, axle, axioms, registry, frontier = fixture()
        ledger["p-negative"] = {
            "target": "Brockian.Foundation.core", "backend": "codex",
            "verdict": "REFUTED", "polarity": "not-p",
        }
        ledger["p-clean"]["polarity"] = "p"
        report = pa.build_report(
            ledger=ledger, best=best, axle=axle, axioms=axioms,
            registry=registry, frontier=frontier, now=NOW,
        )
        group = next(g for g in report["proof_groups"] if g["target"] == "Brockian.Foundation.core")
        self.assertTrue(group["disputed"])
        self.assertIsNone(group["winner_project_id"])
        self.assertEqual(group["next_action"], "human_review_dispute")

    def test_backend_routing_uses_empirical_rate_only_after_sample_floor(self):
        entry = {
            "backend_stats": {
                "aristotle": {"submitted": 10, "clean_proofs": 8, "median_latency_s": 100},
                "codex": {"submitted": 10, "clean_proofs": 4, "median_latency_s": 20},
            }
        }
        self.assertEqual(pa._backend_route(entry, "proof_search"), "aristotle")
        entry["backend_stats"]["codex"] = {"submitted": 2, "clean_proofs": 2}
        self.assertEqual(pa._backend_route(entry, "proof_search"), "race")

    def test_registry_fallback_creates_steering_queue(self):
        registry = {"theorems": [
            {"name": "Brockian.Open.goal", "module": "Brockian.Open", "register": "CONJECTURE"}
        ]}
        rows = pa.score_frontier({"entries": []}, registry, [])
        self.assertEqual(rows[0]["target"], "Brockian.Open.goal")

    def test_cli_writes_sanitized_outputs(self):
        ledger, best, axle, axioms, registry, frontier = fixture()
        with tempfile.TemporaryDirectory() as tmp:
            paths = {}
            for name, value in (("ledger", ledger), ("best", best), ("axle", axle),
                                ("axioms", axioms), ("registry", registry), ("frontier", frontier)):
                path = os.path.join(tmp, name + ".json")
                with open(path, "w") as handle:
                    json.dump(value, handle)
                paths[name] = path
            output = os.path.join(tmp, "out.json")
            review = os.path.join(tmp, "review.md")
            argv = []
            for name, path in paths.items():
                argv += ["--" + name, path]
            argv += ["--output", output, "--review", review, "--now", NOW]
            self.assertEqual(pa.main(argv), 0)
            self.assertEqual(json.load(open(output))["summary"]["promotion_ready"], 1)
            self.assertIn("Compounding-value steering", open(review).read())


if __name__ == "__main__":
    unittest.main()
