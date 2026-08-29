import Mathlib
/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Matrix

namespace Chem

/-- The Hückel (adjacency) matrix of the cycle `C₄`: `A i j = 1` exactly when the carbon
atoms `i` and `j` are neighbours in the four-membered ring. -/

lemma quartic_root_iff (mu : ℝ) :
    mu ^ 4 - 4 * mu ^ 2 = 0 ↔ mu = 2 ∨ mu = 0 ∨ mu = -2 := by
  constructor
  · intro h
    have h2 : mu ^ 2 * ((mu - 2) * (mu + 2)) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact Or.inr (Or.inl (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3))
    · rcases mul_eq_zero.mp h3 with h4 | h4
      · exact Or.inl (by linarith)
      · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl) <;> norm_num

