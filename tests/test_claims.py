from __future__ import annotations

import copy
import json
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from validate_claims import validate_registry  # noqa: E402


class ClaimRegistryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.data = json.loads((ROOT / "ledger" / "claims" / "claims.json").read_text())

    def test_committed_registry_is_valid(self) -> None:
        self.assertEqual(validate_registry(self.data), [])

    def test_conditional_claim_must_expose_hypothesis_debt(self) -> None:
        data = copy.deepcopy(self.data)
        data["claims"][3]["hypotheses_carried"] = []
        errors = validate_registry(data)
        self.assertTrue(any("no explicit hypothesis debt" in error for error in errors))

    def test_uniform_claim_must_name_range(self) -> None:
        data = copy.deepcopy(self.data)
        data["claims"][4]["hypotheses_carried"][0]["range"] = "uniformly in moduli"
        errors = validate_registry(data)
        self.assertTrue(any("q <= Q(X) range" in error for error in errors))

    def test_v5_cannot_be_promoted_without_evidence(self) -> None:
        data = copy.deepcopy(self.data)
        data["claims"][0]["verification_level"] = "V5"
        errors = validate_registry(data)
        self.assertTrue(any("V5 requires" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
