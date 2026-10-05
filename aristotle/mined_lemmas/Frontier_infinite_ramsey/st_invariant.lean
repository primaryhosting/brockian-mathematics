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


private lemma st_invariant (hcof : ∀ l : ℕ, {m | l < m} ∈ U) (hA : A ∈ U)
    (hAi : ∀ n ∈ A, {m | c n m = i} ∈ U) :
    ∀ k, (st c i A k).2 ∈ U ∧ (st c i A k).2 ⊆ A := by
  intro k
  induction k with
  | zero => exact ⟨hA, subset_rfl⟩
  | succ k ih =>
      obtain ⟨hmem, hsub⟩ := ih
      have hU : ((st c i A k).2 ∩ {m | (st c i A k).1 < m}) ∈ U := inter_mem hmem (hcof _)
      have hn : pick ((st c i A k).2 ∩ {m | (st c i A k).1 < m}) ∈
          (st c i A k).2 ∩ {m | (st c i A k).1 < m} := pick_mem (Filter.nonempty_of_mem hU)
      have hnA : pick ((st c i A k).2 ∩ {m | (st c i A k).1 < m}) ∈ A := hsub hn.1
      refine ⟨?_, ?_⟩
      · simp only [st, step]
        exact inter_mem hmem (hAi _ hnA)
      · simp only [st, step]
        exact inter_subset_left.trans hsub

