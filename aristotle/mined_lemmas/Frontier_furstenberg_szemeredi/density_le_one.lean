/-
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset

namespace Frontier

open scoped Classical in
/-- The number of elements of `A` below `n`. -/

lemma density_le_one (A : Set ℕ) (n : ℕ) : (countUpTo A n : ℝ) / n ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast countUpTo_le A n

/-- If a set has positive upper density `δ`, then for any `δ' < δ` there are infinitely many
`n` with at least `δ' * n` elements of `A` below `n`. -/
