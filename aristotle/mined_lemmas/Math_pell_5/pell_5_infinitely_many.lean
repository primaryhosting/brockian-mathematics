/-!
# Pell 5
Category: Pure Mathematics
Target: Math.pell_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 5`.** The equation `x² - 5·y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0` (so that `x ≠ ±1`): take `(x, y) = (9, 4)`,
since `9² - 5·4² = 81 - 80 = 1`. -/

theorem pell_5_infinitely_many (N : ℤ) :
    ∃ x y : ℤ, x ^ 2 - 5 * y ^ 2 = 1 ∧ N < y := by
  refine ⟨(pellSeq5 N.toNat).1, (pellSeq5 N.toNat).2, pellSeq5_isSolution _, ?_⟩
  have h := (pellSeq5_grows N.toNat).2
  have : N ≤ (N.toNat : ℤ) := Int.self_le_toNat N
  omega

/-- The set of nontrivial solutions of `x² - 5·y² = 1` is infinite. -/
