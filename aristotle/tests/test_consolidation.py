import pathlib
import tempfile
import unittest

from aristotle import harvest_proofs
from aristotle.proof_identity import (
    artifact_filenames,
    declaration_signatures,
    harvested_source_path,
    normalize_source,
    target_is_represented,
)


class ProofIdentityTests(unittest.TestCase):
    def test_signature_tracks_namespace_and_multiline_header(self):
        source = """import Mathlib
namespace Alpha
theorem beta
    (n : Nat) :
    n = n := by
  rfl
end Alpha
"""
        declarations = declaration_signatures(source)
        self.assertEqual(declarations[0]["name"], "Alpha.beta")
        self.assertIn("theorem beta (n : Nat) : n = n", declarations[0]["signature"])
        self.assertTrue(target_is_represented("Alpha.beta", declarations))

    def test_collision_safe_artifact_names(self):
        mapping = artifact_filenames(["Brockian.D5_card", "Brockian.D5.card"])
        self.assertEqual(len(set(mapping.values())), 2)
        self.assertIn("Brockian_D5_card.lean", mapping.values())

    def test_full_uuid_source_preferred_over_legacy_prefix(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            project_id = "01234567-89ab-cdef-0123-456789abcdef"
            legacy = root / "admin_01234567.lean"
            full = root / f"admin_{project_id}.lean"
            legacy.write_text("legacy")
            full.write_text("full")
            self.assertEqual(harvested_source_path(root, "admin", project_id), full)

    def test_transport_normalization_only(self):
        self.assertEqual(normalize_source("a  \r\n\r\n"), "a\n")


class HarvestCounterTests(unittest.TestCase):
    def test_current_ledger_ids_are_a_set(self):
        night = {
            "A": {"ids": [{"project_id": "one"}, {"project_id": "two"}]},
            "B": {"ids": [{"project_id": "two"}]},
        }
        self.assertEqual(harvest_proofs.night_job_ids(night), {"one", "two"})


if __name__ == "__main__":
    unittest.main()
