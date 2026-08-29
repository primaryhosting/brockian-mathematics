/-
# Mergesort Correct
Category: Computer Science
Target: CS.mergesort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

variable {α : Type*} [LinearOrder α]

/-- Merge two lists, taking the smaller head at each step. -/

theorem pairwise_merge {l₁ l₂ : List α} (h₁ : List.Pairwise (· ≤ ·) l₁)
    (h₂ : List.Pairwise (· ≤ ·) l₂) : List.Pairwise (· ≤ ·) (merge l₁ l₂) := by
  induction l₁, l₂ using merge.induct with
  | case1 l => simpa [merge] using h₂
  | case2 l h => cases l <;> simp_all [merge]
  | case3 a as b bs hab ih =>
      rw [List.pairwise_cons] at h₁
      rw [merge]
      simp only [hab, if_true, List.pairwise_cons]
      refine ⟨?_, ih h₁.2 h₂⟩
      intro x hx
      rcases List.mem_append.mp ((merge_perm as (b :: bs)).mem_iff.mp hx) with hx | hx
      · exact h₁.1 x hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hab
        · exact le_trans hab ((List.pairwise_cons.mp h₂).1 x hx)
  | case4 a as b bs hab ih =>
      rw [List.pairwise_cons] at h₂
      have hba : b ≤ a := le_of_not_ge hab
      rw [merge]
      simp only [hab, if_false, List.pairwise_cons]
      refine ⟨?_, ih h₁ h₂.2⟩
      intro x hx
      rcases List.mem_append.mp ((merge_perm (a :: as) bs).mem_iff.mp hx) with hx | hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact hba
        · exact le_trans hba ((List.pairwise_cons.mp h₁).1 x hx)
      · exact h₂.1 x hx

/-- `mergeSort` returns a permutation of its input. -/
