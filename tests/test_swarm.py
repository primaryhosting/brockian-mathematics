import tempfile
import unittest
from pathlib import Path

from swarm.gates import source_gate, statement_gate
from swarm.model import ClaimKind, Task
from swarm.planner import ready
from swarm.program import load, validate
from swarm.prompts import render
from swarm.store import EvidenceStore, canonical


class SwarmTests(unittest.TestCase):
    def test_task_roundtrip(self):
        task = Task("t", "M", "x", "theorem x : True", ClaimKind.PROVE, ("a",))
        self.assertEqual(Task.from_dict(task.to_dict()), task)

    def test_program_valid(self):
        tasks = load("swarm/programs/phase_depth.json")
        self.assertEqual(validate(tasks), [])
        self.assertEqual(len(tasks), 6)

    def test_unknown_prerequisite(self):
        self.assertTrue(validate([Task("t", "M", "x", "s", prerequisites=("missing",))]))

    def test_duplicate_id(self):
        t = Task("t", "M", "x", "s")
        self.assertIn("duplicate task id", validate([t, t]))

    def test_ready_respects_dependencies_and_lock(self):
        a = Task("a", "M", "a", "s")
        b = Task("b", "M", "b", "s", prerequisites=("a",))
        c = Task("c", "M", "c", "s", unlocked=False)
        self.assertEqual([x.id for x in ready([a, b, c], set())], ["a"])
        self.assertEqual([x.id for x in ready([a, b, c], {"a"})], ["a", "b"])

    def test_prompt_forbids_self_verification(self):
        prompt = render(Task("t", "M", "x", "theorem x : True"), "prover")
        self.assertIn("Never claim verified/proved", prompt)

    def test_statement_lock(self):
        task = Task("t", "M", "x", "theorem x : True")
        self.assertTrue(statement_gate(task, "theorem x : True := by trivial").passed)
        self.assertFalse(statement_gate(task, "theorem x : False := by").passed)

    def test_holes_rejected(self):
        for token in ("sorry", "admit", "native_decide"):
            self.assertFalse(source_gate(f"theorem x : True := by {token}").passed)
        self.assertTrue(source_gate("theorem x : True := by trivial").passed)

    def test_store_roundtrip_and_audit(self):
        with tempfile.TemporaryDirectory() as root:
            store = EvidenceStore(root)
            record = store.append("test", {"x": 1})
            self.assertEqual(store.get(record["ref"]), {"x": 1})
            self.assertEqual(store.verify(), [])

    def test_store_detects_tamper(self):
        with tempfile.TemporaryDirectory() as root:
            store = EvidenceStore(root)
            record = store.append("test", {"x": 1})
            (Path(root) / "objects" / f"{record['ref']}.json").write_text("{}")
            self.assertTrue(store.verify())

    def test_canonical_is_stable(self):
        self.assertEqual(canonical({"b": 2, "a": 1}), canonical({"a": 1, "b": 2}))


if __name__ == "__main__":
    unittest.main()
