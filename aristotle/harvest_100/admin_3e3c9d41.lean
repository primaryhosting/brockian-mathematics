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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

variable {α : Type*}

/-- Merge two lists with respect to a boolean comparison `le`. -/
def merge (le : α → α → Bool) : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if le x y then x :: merge le xs (y :: ys) else y :: merge le (x :: xs) ys
termination_by xs ys => xs.length + ys.length

/-- Merge sort: split the list in half, sort each half recursively, and merge. -/
def msort (le : α → α → Bool) : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: t =>
      merge le (msort le ((x :: y :: t).take ((t.length + 2) / 2)))
               (msort le ((x :: y :: t).drop ((t.length + 2) / 2)))
termination_by l => l.length
decreasing_by
  · simp only [List.length_take, List.length_cons]; omega
  · simp only [List.length_drop, List.length_cons]; omega

/-- Merging produces a permutation of the concatenation of the two inputs. -/
theorem merge_perm (le : α → α → Bool) (xs ys : List α) :
    (merge le xs ys).Perm (xs ++ ys) := by
  induction xs, ys using CS.merge.induct (le := le) with
  | case1 ys => simp [merge]
  | case2 xs h => simp [merge]
  | case3 x xs y ys h ih =>
      rw [merge]; simp only [h, if_true]
      exact (ih.cons x).trans (by simp)
  | case4 x xs y ys h ih =>
      rw [merge]; simp only [h, if_false, Bool.false_eq_true]
      exact (ih.cons y).trans List.perm_middle.symm

theorem mem_merge {le : α → α → Bool} {xs ys : List α} {a : α} :
    a ∈ merge le xs ys ↔ a ∈ xs ∨ a ∈ ys := by
  rw [(merge_perm le xs ys).mem_iff, List.mem_append]

/-- Merging two sorted lists gives a sorted list. -/
theorem merge_pairwise (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b ∨ le b a) (xs ys : List α)
    (hx : xs.Pairwise (fun a b => le a b = true))
    (hy : ys.Pairwise (fun a b => le a b = true)) :
    (merge le xs ys).Pairwise (fun a b => le a b = true) := by
  induction xs, ys using CS.merge.induct (le := le) with
  | case1 ys => simpa [merge] using hy
  | case2 xs h => simpa [merge] using hx
  | case3 x xs y ys h ih =>
      rw [List.pairwise_cons] at hx
      rw [merge]; simp only [h, if_true, List.pairwise_cons]
      refine ⟨?_, ih hx.2 hy⟩
      intro a ha
      rcases mem_merge.1 ha with ha | ha
      · exact hx.1 a ha
      · rcases List.mem_cons.1 ha with rfl | ha
        · exact h
        · exact trans _ _ _ h ((List.pairwise_cons.1 hy).1 a ha)
  | case4 x xs y ys h ih =>
      have hyx : le y x = true := by
        rcases total x y with h' | h'
        · exact absurd h' h
        · exact h'
      rw [List.pairwise_cons] at hy
      rw [merge]; simp only [h, if_false, Bool.false_eq_true, List.pairwise_cons]
      refine ⟨?_, ih hx hy.2⟩
      intro a ha
      rcases mem_merge.1 ha with ha | ha
      · rcases List.mem_cons.1 ha with rfl | ha
        · exact hyx
        · exact trans _ _ _ hyx ((List.pairwise_cons.1 hx).1 a ha)
      · exact hy.1 a ha

/-- `msort` returns a permutation of its input. -/
theorem msort_perm (le : α → α → Bool) (l : List α) : (msort le l).Perm l := by
  induction l using CS.msort.induct with
  | case1 => simp [msort]
  | case2 x => simp [msort]
  | case3 x y t ih1 ih2 =>
      rw [msort]
      refine (merge_perm le _ _).trans ?_
      exact (ih1.append ih2).trans (by rw [List.take_append_drop])

/-- `msort` returns a sorted list, for any transitive and total comparison. -/
theorem msort_pairwise (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b ∨ le b a) (l : List α) :
    (msort le l).Pairwise (fun a b => le a b = true) := by
  induction l using CS.msort.induct with
  | case1 => simp [msort]
  | case2 x => simp [msort]
  | case3 x y t ih1 ih2 =>
      rw [msort]
      exact merge_pairwise le trans total _ _ ih1 ih2

/-- **Correctness of merge sort**: for a transitive and total boolean comparison `le`,
`msort le l` is sorted with respect to `le` and is a permutation of `l`. -/
theorem mergesort_correct (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b ∨ le b a) (l : List α) :
    List.Pairwise (fun a b => le a b = true) (msort le l) ∧ (msort le l).Perm l :=
  ⟨msort_pairwise le trans total l, msort_perm le l⟩

/-- Correctness of merge sort on a linear order, using `(· ≤ ·)` as the comparison. -/
theorem mergesort_correct_linearOrder [LinearOrder α] (l : List α) :
    List.Pairwise (· ≤ ·) (msort (fun a b => decide (a ≤ b)) l) ∧
      (msort (fun a b => decide (a ≤ b)) l).Perm l := by
  refine ⟨?_, msort_perm _ l⟩
  have := msort_pairwise (α := α) (fun a b => decide (a ≤ b))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; exact le_trans hab hbc)
    (by intro a b; simp only [decide_eq_true_eq]; exact le_total a b) l
  simpa using this

end CS

