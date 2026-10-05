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
def merge : List α → List α → List α
  | [], l => l
  | l, [] => l
  | a :: as, b :: bs => if a ≤ b then a :: merge as (b :: bs) else b :: merge (a :: as) bs
  termination_by l₁ l₂ => l₁.length + l₂.length

/-- Top-down mergesort: split in half, sort each half recursively, merge the results. -/
def mergeSort : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: l =>
      merge (mergeSort ((a :: b :: l).take ((a :: b :: l).length / 2)))
        (mergeSort ((a :: b :: l).drop ((a :: b :: l).length / 2)))
  termination_by l => l.length
  decreasing_by
    · simp only [List.length_take, List.length_cons]
      omega
    · simp only [List.length_drop, List.length_cons]
      omega

/-- `merge` produces a permutation of the concatenation of its arguments. -/
theorem merge_perm (l₁ l₂ : List α) : List.Perm (merge l₁ l₂) (l₁ ++ l₂) := by
  induction l₁, l₂ using merge.induct with
  | case1 l => simp [merge]
  | case2 l h => cases l <;> simp [merge]
  | case3 a as b bs h ih =>
      rw [merge]
      simp only [h, if_true, List.cons_append]
      exact ih.cons a
  | case4 a as b bs h ih =>
      rw [merge]
      simp only [h, if_false]
      exact (ih.cons b).trans List.perm_middle.symm

/-- Merging two sorted lists yields a sorted list. -/
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
theorem mergeSort_perm (l : List α) : List.Perm (mergeSort l) l := by
  induction l using mergeSort.induct with
  | case1 => simp [mergeSort]
  | case2 a => simp [mergeSort]
  | case3 a b l ih₁ ih₂ =>
      rw [mergeSort]
      refine (merge_perm _ _).trans ?_
      refine (ih₁.append ih₂).trans ?_
      simp

/-- `mergeSort` returns a sorted list. -/
theorem pairwise_mergeSort (l : List α) : List.Pairwise (· ≤ ·) (mergeSort l) := by
  induction l using mergeSort.induct with
  | case1 => simp [mergeSort]
  | case2 a => simp [mergeSort]
  | case3 a b l ih₁ ih₂ =>
      rw [mergeSort]
      exact pairwise_merge ih₁ ih₂

/-- **Mergesort is correct**: `mergeSort` returns a sorted permutation of its input. -/
theorem mergesort_correct (l : List α) :
    List.Pairwise (· ≤ ·) (mergeSort l) ∧ List.Perm (mergeSort l) l :=
  ⟨pairwise_mergeSort l, mergeSort_perm l⟩

end CS

