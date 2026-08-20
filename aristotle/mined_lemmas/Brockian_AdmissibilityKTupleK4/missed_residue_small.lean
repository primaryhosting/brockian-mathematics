/-!
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, stated from first principles:
`p` is at least `2` and its only divisors are `1` and `p`. -/

theorem missed_residue_small : ∀ q < 9, 2 ≤ q → ∃ a < q, ∀ h ∈ [0, 2, 6, 8], h % q ≠ a := by
  decide

/-- For a modulus `q ≥ 9` the residue class `1` is avoided, since each shift is `< q`
and none of them equals `1`. -/
