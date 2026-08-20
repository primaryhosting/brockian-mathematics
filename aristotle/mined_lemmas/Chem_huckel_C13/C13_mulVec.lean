import Mathlib
/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex Matrix

namespace Chem

/-- A primitive 13-th root of unity. -/

lemma C13_mulVec (v : ZMod 13 → ℂ) (i : ZMod 13) :
    (C13 *ᵥ v) i = v (i + 1) + v (i - 1) := by
  have key : ∀ j : ZMod 13, (if j = i + 1 ∨ j = i - 1 then (1 : ℂ) else 0) * v j
      = (if j = i + 1 then v j else 0) + (if j = i - 1 then v j else 0) := by
    intro j
    rcases eq_or_ne j (i + 1) with h1 | h1
    · simp [h1, succ_ne_pred i]
    · rcases eq_or_ne j (i - 1) with h2 | h2
      · simp [h2, (succ_ne_pred i).symm]
      · simp [h1, h2]
  simp only [Matrix.mulVec, dotProduct, C13, Matrix.of_apply]
  simp_rw [key]
  rw [Finset.sum_add_distrib]
  simp

/-- The eigenvalue attached to the character index `k`. -/
