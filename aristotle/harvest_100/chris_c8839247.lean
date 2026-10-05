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

/-- Split a list into two lists by alternately distributing its elements. -/
def split : List α → List α × List α
  | [] => ([], [])
  | a :: l => ((split l).2, a :: (split l).1)

theorem split_perm (l : List α) : ((split l).1 ++ (split l).2).Perm l := by
  induction l with
  | nil => simp [split]
  | cons a l ih =>
      show ((split l).2 ++ a :: (split l).1).Perm (a :: l)
      refine List.Perm.trans List.perm_middle ?_
      exact List.Perm.cons a ((List.perm_append_comm).trans ih)

theorem split_length (l : List α) :
    (split l).1.length ≤ l.length ∧ (split l).2.length ≤ l.length := by
  induction l with
  | nil => simp [split]
  | cons a l ih =>
      constructor
      · show (split l).2.length ≤ l.length + 1
        omega
      · show ((split l).1).length + 1 ≤ l.length + 1
        omega

theorem split_length_fst_le (l : List α) : (split l).1.length ≤ l.length := (split_length l).1

theorem split_length_snd_le (l : List α) : (split l).2.length ≤ l.length := (split_length l).2

/-- Merge two lists with respect to a boolean comparison `le`. -/
def merge (le : α → α → Bool) : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if le x y then x :: merge le xs (y :: ys) else y :: merge le (x :: xs) ys
  termination_by xs ys => xs.length + ys.length

@[simp] theorem merge_nil_left (le : α → α → Bool) (ys : List α) : merge le [] ys = ys := by
  cases ys <;> simp [merge]

@[simp] theorem merge_nil_right (le : α → α → Bool) (xs : List α) : merge le xs [] = xs := by
  cases xs <;> simp [merge]

theorem merge_cons_cons (le : α → α → Bool) (x y : α) (xs ys : List α) :
    merge le (x :: xs) (y :: ys) =
      if le x y then x :: merge le xs (y :: ys) else y :: merge le (x :: xs) ys := by
  rw [merge]

theorem merge_perm (le : α → α → Bool) : ∀ xs ys : List α, (merge le xs ys).Perm (xs ++ ys) := by
  intro xs ys
  induction xs, ys using merge.induct (le := le) with
  | case1 ys => simp
  | case2 xs h => simp
  | case3 x xs y ys h ih =>
      rw [merge_cons_cons, if_pos h]
      exact (ih.cons x)
  | case4 x xs y ys h ih =>
      rw [merge_cons_cons, if_neg h]
      refine List.Perm.trans (ih.cons y) ?_
      exact (List.perm_middle (a := y) (l₁ := x :: xs) (l₂ := ys)).symm

theorem mem_merge {le : α → α → Bool} {a : α} {xs ys : List α} :
    a ∈ merge le xs ys ↔ a ∈ xs ∨ a ∈ ys := by
  rw [(merge_perm le xs ys).mem_iff, List.mem_append]

theorem merge_sorted {le : α → α → Bool}
    (htrans : ∀ a b c, le a b → le b c → le a c)
    (htotal : ∀ a b, le a b ∨ le b a) :
    ∀ xs ys : List α, List.Pairwise (fun a b => le a b = true) xs →
      List.Pairwise (fun a b => le a b = true) ys →
      List.Pairwise (fun a b => le a b = true) (merge le xs ys) := by
  intro xs ys
  induction xs, ys using merge.induct (le := le) with
  | case1 ys => simp
  | case2 xs h => simp
  | case3 x xs y ys h ih =>
      intro hx hy
      rw [merge_cons_cons, if_pos h]
      rw [List.pairwise_cons] at hx ⊢
      refine ⟨?_, ih hx.2 hy⟩
      intro z hz
      rcases mem_merge.1 hz with hz | hz
      · exact hx.1 z hz
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact h
        · exact htrans x y z h ((List.pairwise_cons.1 hy).1 z hz)
  | case4 x xs y ys h ih =>
      intro hx hy
      rw [merge_cons_cons, if_neg h]
      have hyx : le y x = true := by
        rcases htotal x y with h' | h'
        · exact absurd h' h
        · exact h'
      rw [List.pairwise_cons] at hy ⊢
      refine ⟨?_, ih hx hy.2⟩
      intro z hz
      rcases mem_merge.1 hz with hz | hz
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact hyx
        · exact htrans y x z hyx ((List.pairwise_cons.1 hx).1 z hz)
      · exact hy.1 z hz

/-- Mergesort with respect to a boolean comparison `le`. -/
def mergesort (le : α → α → Bool) : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: l =>
      merge le (mergesort le (a :: (split l).1)) (mergesort le (b :: (split l).2))
  termination_by l => l.length
  decreasing_by
    · have := split_length_fst_le l
      simp only [List.length_cons]
      omega
    · have := split_length_snd_le l
      simp only [List.length_cons]
      omega

theorem mergesort_cons_cons (le : α → α → Bool) (a b : α) (l : List α) :
    mergesort le (a :: b :: l) =
      merge le (mergesort le (a :: (split l).1)) (mergesort le (b :: (split l).2)) := by
  rw [mergesort]

theorem mergesort_perm (le : α → α → Bool) : ∀ l : List α, (mergesort le l).Perm l := by
  intro l
  induction l using mergesort.induct with
  | case1 => simp [mergesort]
  | case2 a => simp [mergesort]
  | case3 a b l ih1 ih2 =>
      rw [mergesort_cons_cons]
      refine (merge_perm le _ _).trans ?_
      refine (List.Perm.append ih1 ih2).trans ?_
      show ((a :: (split l).1) ++ (b :: (split l).2)).Perm (a :: b :: l)
      refine List.Perm.cons a ?_
      refine List.Perm.trans List.perm_middle ?_
      exact List.Perm.cons b (split_perm l)

theorem mergesort_sorted {le : α → α → Bool}
    (htrans : ∀ a b c, le a b → le b c → le a c)
    (htotal : ∀ a b, le a b ∨ le b a) :
    ∀ l : List α, List.Pairwise (fun a b => le a b = true) (mergesort le l) := by
  intro l
  induction l using mergesort.induct with
  | case1 => simp [mergesort]
  | case2 a => simp [mergesort]
  | case3 a b l ih1 ih2 =>
      rw [mergesort_cons_cons]
      exact merge_sorted htrans htotal _ _ ih1 ih2

/-- **Mergesort is correct**: for a transitive and total boolean comparison `le`,
`mergesort le l` is sorted with respect to `le` and is a permutation of `l`. -/
theorem mergesort_correct (le : α → α → Bool)
    (htrans : ∀ a b c, le a b → le b c → le a c)
    (htotal : ∀ a b, le a b ∨ le b a) (l : List α) :
    List.Pairwise (fun a b => le a b = true) (mergesort le l) ∧ (mergesort le l).Perm l :=
  ⟨mergesort_sorted htrans htotal l, mergesort_perm le l⟩

/-- Concrete instance: sorting a list of natural numbers with `fun a b => decide (a ≤ b)`. -/
theorem mergesort_correct_nat (l : List Nat) :
    List.Pairwise (fun a b => a ≤ b) (mergesort (fun a b => decide (a ≤ b)) l) ∧
      (mergesort (fun a b => decide (a ≤ b)) l).Perm l := by
  have h := mergesort_correct (fun a b => decide (a ≤ b))
    (by intro a b c hab hbc; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; by_cases h : a ≤ b <;> simp [h] <;> omega) l
  refine ⟨?_, h.2⟩
  have := h.1
  simpa using this

end CS

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

