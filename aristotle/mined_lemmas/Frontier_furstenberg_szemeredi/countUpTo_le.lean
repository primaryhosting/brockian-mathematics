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

lemma countUpTo_le (A : Set ℕ) (n : ℕ) : countUpTo A n ≤ n := by
  classical
  simpa [countUpTo] using
    (Finset.card_le_card (Finset.filter_subset (· ∈ A) (Finset.range n))).trans_eq
      (Finset.card_range n)

