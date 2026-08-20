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

lemma isCoboundedUnder_density (A : Set ℕ) :
    IsCoboundedUnder (· ≤ ·) atTop (fun n : ℕ => (countUpTo A n : ℝ) / n) := by
  refine Filter.IsBoundedUnder.isCoboundedUnder_le ⟨0, ?_⟩
  simp only [Filter.eventually_map]
  filter_upwards with n
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

