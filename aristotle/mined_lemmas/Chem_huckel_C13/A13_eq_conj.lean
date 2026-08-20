import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped Real

namespace Chem

/-! ### A primitive 13-th root of unity -/

/-- A primitive 13-th root of unity. -/

lemma A13_eq_conj : A13 = P13 * D13 * P13⁻¹ := by
  have hinv : P13 * P13⁻¹ = 1 := Matrix.mul_nonsing_inv _ P13_isUnit_det
  calc A13 = A13 * (P13 * P13⁻¹) := by rw [hinv, mul_one]
    _ = A13 * P13 * P13⁻¹ := by rw [Matrix.mul_assoc]
    _ = P13 * D13 * P13⁻¹ := by rw [A13_mul_P13]

/-- **Hückel theory for C₁₃**: the adjacency eigenvalues of the cycle graph `C₁₃` are exactly
the numbers `2 cos (2πk/13)` for `k = 0, …, 12`. -/
