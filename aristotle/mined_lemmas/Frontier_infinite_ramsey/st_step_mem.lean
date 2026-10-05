import Mathlib
/-!
# Infinite Ramsey
Category: Frontier — Set Theory
Target: Frontier.infinite_ramsey
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Filter Set


private lemma st_step_mem (hcof : ∀ l : ℕ, {m | l < m} ∈ U) (hA : A ∈ U)
    (hAi : ∀ n ∈ A, {m | c n m = i} ∈ U) (k : ℕ) :
    (st c i A (k + 1)).1 ∈ (st c i A k).2 ∧ (st c i A k).1 < (st c i A (k + 1)).1 := by
  obtain ⟨hmem, _⟩ := st_invariant hcof hA hAi k
  have hn : pick ((st c i A k).2 ∩ {m | (st c i A k).1 < m}) ∈
      (st c i A k).2 ∩ {m | (st c i A k).1 < m} :=
    pick_mem (Filter.nonempty_of_mem (inter_mem hmem (hcof _)))
  exact ⟨hn.1, hn.2⟩

