import Mathlib
import RequestProject.Main

/-!
# Mergesort on a linear order

A Mathlib-facing corollary of `CS.mergesort_correct`: on any linear order,
`CS.mergeSort (· ≤ ·)` produces a `List.Sorted (· ≤ ·)` permutation of its input.
-/

namespace CS

/-- On a linear order, `mergeSort (· ≤ ·) l` is sorted and a permutation of `l`. -/
theorem mergesort_correct_linearOrder {α : Type*} [LinearOrder α] (l : List α) :
    List.Pairwise (· ≤ ·) (CS.mergeSort (· ≤ · : α → α → Prop) l) ∧
      (CS.mergeSort (· ≤ · : α → α → Prop) l).Perm l :=
  CS.mergesort_correct _ le_total (fun _ _ _ hab hbc => le_trans hab hbc) l

end CS

/-!
# Mergesort Correct
Category: Computer Science
Target: CS.mergesort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to be the very first
commands in a file, and a module doc comment `/-! ... -/` may not precede them.
Since the header comment above must literally begin the file, this module is
written to be self-contained (it needs no imports beyond the prelude).
A Mathlib-facing corollary for linear orders lives in
`RequestProject/LinearOrderCorollary.lean`.
-/

set_option autoImplicit false

namespace CS

universe u

variable {α : Type u}

/-- Merge two lists with respect to a decidable relation `r`. -/
def merge (r : α → α → Prop) [DecidableRel r] : List α → List α → List α
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => if r x y then x :: merge r xs (y :: ys) else y :: merge r (x :: xs) ys
termination_by xs ys => xs.length + ys.length

/-- Split a list into two lists by alternating elements. -/
def split : List α → List α × List α
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: t => (x :: (split t).1, y :: (split t).2)

theorem split_perm : ∀ l : List α, ((split l).1 ++ (split l).2).Perm l
  | [] => by simp [split]
  | [_] => by simp [split]
  | x :: y :: t => by
      have ih := split_perm t
      simp only [split, List.cons_append]
      refine List.Perm.cons x ?_
      exact (List.perm_middle).trans ((ih).cons y)

theorem split_length_add (l : List α) :
    (split l).1.length + (split l).2.length = l.length := by
  have h := (split_perm l).length_eq
  simpa using h

theorem split_fst_length_lt (x y : α) (t : List α) :
    (split (x :: y :: t)).1.length < (x :: y :: t).length := by
  have h := split_length_add t
  simp only [split, List.length_cons]
  omega

theorem split_snd_length_lt (x y : α) (t : List α) :
    (split (x :: y :: t)).2.length < (x :: y :: t).length := by
  have h := split_length_add t
  simp only [split, List.length_cons]
  omega

/-- Mergesort: split the list in two, sort each half recursively, and merge. -/
def mergeSort (r : α → α → Prop) [DecidableRel r] : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: t =>
      merge r (mergeSort r (split (x :: y :: t)).1) (mergeSort r (split (x :: y :: t)).2)
termination_by l => l.length
decreasing_by
  · exact split_fst_length_lt x y t
  · exact split_snd_length_lt x y t

theorem merge_perm (r : α → α → Prop) [DecidableRel r] :
    ∀ xs ys : List α, (merge r xs ys).Perm (xs ++ ys)
  | [], ys => by rw [merge]; simp
  | x :: xs, [] => by rw [merge] <;> simp
  | x :: xs, y :: ys => by
      by_cases h : r x y
      · rw [merge, if_pos h]
        exact (merge_perm r xs (y :: ys)).cons x
      · rw [merge, if_neg h]
        refine ((merge_perm r (x :: xs) ys).cons y).trans ?_
        exact (List.perm_middle (a := y) (l₁ := x :: xs) (l₂ := ys)).symm
termination_by xs ys => xs.length + ys.length

theorem mem_merge {r : α → α → Prop} [DecidableRel r] {a : α} {xs ys : List α} :
    a ∈ merge r xs ys ↔ a ∈ xs ∨ a ∈ ys := by
  rw [(merge_perm r xs ys).mem_iff, List.mem_append]

theorem merge_pairwise (r : α → α → Prop) [DecidableRel r]
    (htotal : ∀ a b : α, r a b ∨ r b a) (htrans : ∀ a b c : α, r a b → r b c → r a c) :
    ∀ xs ys : List α, List.Pairwise r xs → List.Pairwise r ys →
      List.Pairwise r (merge r xs ys)
  | [], ys, _, hy => by rw [merge]; exact hy
  | x :: xs, [], hx, _ => by
      rw [merge]
      · exact hx
      · simp
  | x :: xs, y :: ys, hx, hy => by
      rw [List.pairwise_cons] at hx hy
      by_cases h : r x y
      · rw [merge, if_pos h, List.pairwise_cons]
        refine ⟨?_, merge_pairwise r htotal htrans xs (y :: ys) hx.2
          (List.pairwise_cons.mpr hy)⟩
        intro b hb
        rcases mem_merge.mp hb with hb | hb
        · exact hx.1 b hb
        · rcases List.mem_cons.mp hb with rfl | hb
          · exact h
          · exact htrans x y b h (hy.1 b hb)
      · rw [merge, if_neg h, List.pairwise_cons]
        refine ⟨?_, merge_pairwise r htotal htrans (x :: xs) ys
          (List.pairwise_cons.mpr hx) hy.2⟩
        have hyx : r y x := (htotal x y).resolve_left h
        intro b hb
        rcases mem_merge.mp hb with hb | hb
        · rcases List.mem_cons.mp hb with rfl | hb
          · exact hyx
          · exact htrans y x b hyx (hx.1 b hb)
        · exact hy.1 b hb
termination_by xs ys => xs.length + ys.length

theorem mergeSort_perm (r : α → α → Prop) [DecidableRel r] :
    ∀ l : List α, (mergeSort r l).Perm l
  | [] => by rw [mergeSort]
  | [x] => by rw [mergeSort]
  | x :: y :: t => by
      have h1 : (mergeSort r (split (x :: y :: t)).1).Perm (split (x :: y :: t)).1 :=
        mergeSort_perm r _
      have h2 : (mergeSort r (split (x :: y :: t)).2).Perm (split (x :: y :: t)).2 :=
        mergeSort_perm r _
      rw [mergeSort]
      exact (merge_perm r _ _).trans ((h1.append h2).trans (split_perm (x :: y :: t)))
termination_by l => l.length
decreasing_by
  · exact split_fst_length_lt x y t
  · exact split_snd_length_lt x y t

theorem mergeSort_pairwise (r : α → α → Prop) [DecidableRel r]
    (htotal : ∀ a b : α, r a b ∨ r b a) (htrans : ∀ a b c : α, r a b → r b c → r a c) :
    ∀ l : List α, List.Pairwise r (mergeSort r l)
  | [] => by rw [mergeSort]; exact List.Pairwise.nil
  | [x] => by rw [mergeSort]; simp
  | x :: y :: t => by
      rw [mergeSort]
      exact merge_pairwise r htotal htrans _ _
        (mergeSort_pairwise r htotal htrans (split (x :: y :: t)).1)
        (mergeSort_pairwise r htotal htrans (split (x :: y :: t)).2)
termination_by l => l.length
decreasing_by
  · exact split_fst_length_lt x y t
  · exact split_snd_length_lt x y t

/-- **Mergesort is correct**: for a total, transitive (decidable) relation `r`,
`mergeSort r l` is sorted with respect to `r` (i.e. pairwise `r`-related, in order)
and is a permutation of the input list `l`. -/
theorem mergesort_correct (r : α → α → Prop) [DecidableRel r]
    (htotal : ∀ a b : α, r a b ∨ r b a) (htrans : ∀ a b c : α, r a b → r b c → r a c)
    (l : List α) :
    List.Pairwise r (mergeSort r l) ∧ (mergeSort r l).Perm l :=
  ⟨mergeSort_pairwise r htotal htrans l, mergeSort_perm r l⟩

end CS

