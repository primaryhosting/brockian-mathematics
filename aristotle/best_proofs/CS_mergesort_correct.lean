import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

variable {α : Type*} [LinearOrder α]

/-- Merge two lists, assumed sorted, into one list. -/
def merge : List α → List α → List α
  | [], l => l
  | l, [] => l
  | a :: as, b :: bs => if a ≤ b then a :: merge as (b :: bs) else b :: merge (a :: as) bs
  termination_by l₁ l₂ => l₁.length + l₂.length

/-- Merge sort: split the list in half, sort both halves, merge them. -/
def mergeSort : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: t =>
      let l := a :: b :: t
      merge (mergeSort (l.take (l.length / 2))) (mergeSort (l.drop (l.length / 2)))
  termination_by l => l.length
  decreasing_by
  · simp only [List.length_take, List.length_cons]
    omega
  · simp only [List.length_drop, List.length_cons]
    omega

@[simp] theorem merge_nil_left (l : List α) : merge [] l = l := by
  cases l <;> simp [merge]

@[simp] theorem merge_nil_right (l : List α) : merge l [] = l := by
  cases l <;> simp [merge]

theorem merge_cons_cons (a b : α) (as bs : List α) :
    merge (a :: as) (b :: bs) =
      if a ≤ b then a :: merge as (b :: bs) else b :: merge (a :: as) bs := by
  simp [merge]

theorem merge_perm : ∀ l₁ l₂ : List α, (merge l₁ l₂).Perm (l₁ ++ l₂)
  | [], l => by simp
  | a :: as, [] => by simp
  | a :: as, b :: bs => by
      rw [merge_cons_cons]
      split
      · exact ((merge_perm as (b :: bs)).cons a)
      · exact ((merge_perm (a :: as) bs).cons b).trans List.perm_middle.symm
  termination_by l₁ l₂ => l₁.length + l₂.length

theorem mem_merge {x : α} {l₁ l₂ : List α} : x ∈ merge l₁ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂ := by
  rw [(merge_perm l₁ l₂).mem_iff, List.mem_append]

theorem sorted_merge : ∀ l₁ l₂ : List α, l₁.Pairwise (· ≤ ·) → l₂.Pairwise (· ≤ ·) →
    (merge l₁ l₂).Pairwise (· ≤ ·)
  | [], l, _, h => by simpa using h
  | a :: as, [], h, _ => by simpa using h
  | a :: as, b :: bs, h₁, h₂ => by
      rw [List.pairwise_cons] at h₁ h₂
      rw [merge_cons_cons]
      split
      · rename_i hab
        rw [List.pairwise_cons]
        refine ⟨?_, sorted_merge as (b :: bs) h₁.2 (List.pairwise_cons.2 h₂)⟩
        intro x hx
        rcases mem_merge.1 hx with hx | hx
        · exact h₁.1 x hx
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact hab
          · exact le_trans hab (h₂.1 x hx)
      · rename_i hab
        have hba : b ≤ a := le_of_not_ge hab
        rw [List.pairwise_cons]
        refine ⟨?_, sorted_merge (a :: as) bs (List.pairwise_cons.2 h₁) h₂.2⟩
        intro x hx
        rcases mem_merge.1 hx with hx | hx
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact hba
          · exact le_trans hba (h₁.1 x hx)
        · exact h₂.1 x hx
  termination_by l₁ l₂ => l₁.length + l₂.length

theorem mergeSort_perm : ∀ l : List α, (mergeSort l).Perm l
  | [] => by simp [mergeSort]
  | [a] => by simp [mergeSort]
  | a :: b :: t => by
      rw [mergeSort]
      refine (merge_perm _ _).trans ?_
      refine ((mergeSort_perm _).append (mergeSort_perm _)).trans ?_
      rw [List.take_append_drop]
  termination_by l => l.length
  decreasing_by
  · simp only [List.length_take, List.length_cons]; omega
  · simp only [List.length_drop, List.length_cons]; omega

theorem sorted_mergeSort : ∀ l : List α, (mergeSort l).Pairwise (· ≤ ·)
  | [] => by simp [mergeSort]
  | [a] => by simp [mergeSort]
  | a :: b :: t => by
      rw [mergeSort]
      exact sorted_merge _ _ (sorted_mergeSort _) (sorted_mergeSort _)
  termination_by l => l.length
  decreasing_by
  · simp only [List.length_take, List.length_cons]; omega
  · simp only [List.length_drop, List.length_cons]; omega

/-- `mergeSort` returns a sorted permutation of its input. -/
theorem mergesort_correct (l : List α) :
    (mergeSort l).Pairwise (· ≤ ·) ∧ (mergeSort l).Perm l :=
  ⟨sorted_mergeSort l, mergeSort_perm l⟩

end CS

