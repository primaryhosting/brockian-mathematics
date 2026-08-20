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

/-!
# Mergesort Correct
Category: Computer Science
Target: CS.mergesort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u

variable {α : Type u}

/-- Merge two lists with respect to a boolean comparison `le`. -/
def merge (le : α → α → Bool) : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if le x y then x :: merge le xs (y :: ys) else y :: merge le (x :: xs) ys
  termination_by xs ys => xs.length + ys.length

/-- Split a list into two lists by alternating its elements. -/
def split : List α → List α × List α
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: t => ((x :: (split t).1), (y :: (split t).2))

theorem split_length_add (l : List α) :
    (split l).1.length + (split l).2.length = l.length := by
  induction l using split.induct with
  | case1 => simp [split]
  | case2 x => simp [split]
  | case3 x y t ih => simp only [split, List.length_cons]; omega

theorem split_perm (l : List α) : ((split l).1 ++ (split l).2).Perm l := by
  induction l using split.induct with
  | case1 => simp [split]
  | case2 x => simp [split]
  | case3 x y t ih =>
      simp only [split, List.cons_append]
      refine List.Perm.trans (List.Perm.cons x ?_) (List.Perm.cons x (List.Perm.cons y ih))
      exact (List.perm_middle (a := y) (l₁ := (split t).1) (l₂ := (split t).2))

/-- Mergesort: split the list in two, sort the halves recursively, and merge them. -/
def mergeSort (le : α → α → Bool) : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: t =>
      merge le (mergeSort le (split (x :: y :: t)).1) (mergeSort le (split (x :: y :: t)).2)
  termination_by l => l.length
  decreasing_by
    · have h := split_length_add (x :: y :: t)
      simp only [split, List.length_cons] at h ⊢
      omega
    · have h := split_length_add (x :: y :: t)
      simp only [split, List.length_cons] at h ⊢
      omega

theorem merge_perm (le : α → α → Bool) (xs ys : List α) :
    (merge le xs ys).Perm (xs ++ ys) := by
  induction xs, ys using merge.induct (le := le) with
  | case1 ys => simp [merge]
  | case2 xs h => cases xs <;> simp_all [merge]
  | case3 x xs y ys h ih =>
      rw [merge, if_pos h]
      exact ih.cons x
  | case4 x xs y ys h ih =>
      rw [merge, if_neg h]
      exact (ih.cons y).trans List.perm_middle.symm

theorem mem_merge {le : α → α → Bool} {a : α} {xs ys : List α} :
    a ∈ merge le xs ys ↔ a ∈ xs ∨ a ∈ ys := by
  rw [(merge_perm le xs ys).mem_iff, List.mem_append]

theorem merge_pairwise (le : α → α → Bool)
    (htotal : ∀ a b, le a b || le b a) (htrans : ∀ a b c, le a b → le b c → le a c)
    {xs ys : List α} (hx : xs.Pairwise (fun a b => le a b = true))
    (hy : ys.Pairwise (fun a b => le a b = true)) :
    (merge le xs ys).Pairwise (fun a b => le a b = true) := by
  induction xs, ys using merge.induct (le := le) with
  | case1 ys => simpa [merge] using hy
  | case2 xs h => cases xs <;> simp_all [merge]
  | case3 x xs y ys h ih =>
      rw [merge, if_pos h]
      rw [List.pairwise_cons] at hx
      refine List.pairwise_cons.2 ⟨?_, ih hx.2 hy⟩
      intro b hb
      rcases mem_merge.1 hb with hb | hb
      · exact hx.1 b hb
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact h
        · exact htrans _ _ _ h ((List.pairwise_cons.1 hy).1 b hb)
  | case4 x xs y ys h ih =>
      rw [merge, if_neg h]
      have hyx : le y x = true := by
        have ht := htotal x y
        simp only [h, Bool.false_or] at ht
        simpa using ht
      rw [List.pairwise_cons] at hy
      refine List.pairwise_cons.2 ⟨?_, ih hx hy.2⟩
      intro b hb
      rcases mem_merge.1 hb with hb | hb
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact hyx
        · exact htrans _ _ _ hyx ((List.pairwise_cons.1 hx).1 b hb)
      · exact hy.1 b hb

theorem mergeSort_perm (le : α → α → Bool) (l : List α) : (mergeSort le l).Perm l := by
  induction l using mergeSort.induct with
  | case1 => simp [mergeSort]
  | case2 x => simp [mergeSort]
  | case3 x y t ih1 ih2 =>
      rw [mergeSort]
      exact (merge_perm _ _ _).trans ((ih1.append ih2).trans (split_perm (x :: y :: t)))

theorem mergeSort_pairwise (le : α → α → Bool)
    (htotal : ∀ a b, le a b || le b a) (htrans : ∀ a b c, le a b → le b c → le a c)
    (l : List α) : (mergeSort le l).Pairwise (fun a b => le a b = true) := by
  induction l using mergeSort.induct with
  | case1 => simp [mergeSort]
  | case2 x => simp [mergeSort]
  | case3 x y t ih1 ih2 =>
      rw [mergeSort]
      exact merge_pairwise le htotal htrans ih1 ih2

/-- **Mergesort is correct**: for any total, transitive boolean comparison `le`,
`mergeSort le l` is a permutation of `l` which is sorted with respect to `le`. -/
theorem mergesort_correct (le : α → α → Bool)
    (htotal : ∀ a b, le a b || le b a) (htrans : ∀ a b c, le a b → le b c → le a c)
    (l : List α) :
    (mergeSort le l).Perm l ∧ (mergeSort le l).Pairwise (fun a b => le a b = true) :=
  ⟨mergeSort_perm le l, mergeSort_pairwise le htotal htrans l⟩

end CS

