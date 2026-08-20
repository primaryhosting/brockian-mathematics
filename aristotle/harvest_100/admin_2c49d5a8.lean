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

variable {α : Type u} (r : α → α → Prop) [DecidableRel r]

/-- Merge two lists with respect to a decidable relation `r`.
The smaller head (according to `r`) is emitted first. -/
def merge : List α → List α → List α
  | [], l => l
  | l, [] => l
  | a :: as, b :: bs =>
      if r a b then a :: merge as (b :: bs) else b :: merge (a :: as) bs
  termination_by xs ys => xs.length + ys.length

/-- Mergesort: split the list into two halves, sort each half recursively, then merge. -/
def mergeSort (l : List α) : List α :=
  match hl : l with
  | [] => []
  | [_] => l
  | _ :: _ :: _ =>
      merge r (mergeSort (l.take (l.length / 2))) (mergeSort (l.drop (l.length / 2)))
  termination_by l.length
  decreasing_by
    · subst hl; simp only [List.length_take, List.length_cons]; omega
    · subst hl; simp only [List.length_drop, List.length_cons]; omega

/-! ### Defining equations -/

theorem merge_nil_left (l : List α) : merge r [] l = l := by rw [merge]

theorem merge_nil_right (l : List α) : merge r l [] = l := by
  cases l with
  | nil => rw [merge_nil_left]
  | cons a t => rw [merge]; simp

theorem merge_cons_cons (a : α) (as : List α) (b : α) (bs : List α) :
    merge r (a :: as) (b :: bs) =
      if r a b then a :: merge r as (b :: bs) else b :: merge r (a :: as) bs := by
  rw [merge]

theorem mergeSort_nil : mergeSort r ([] : List α) = [] := by rw [mergeSort]

theorem mergeSort_singleton (a : α) : mergeSort r [a] = [a] := by rw [mergeSort]

theorem mergeSort_cons_cons (a b : α) (t : List α) :
    mergeSort r (a :: b :: t) =
      merge r (mergeSort r ((a :: b :: t).take ((a :: b :: t).length / 2)))
        (mergeSort r ((a :: b :: t).drop ((a :: b :: t).length / 2))) := by
  rw [mergeSort]

/-! ### Correctness of `merge` -/

/-- `merge r xs ys` is a permutation of `xs ++ ys`. -/
theorem merge_perm (xs ys : List α) : (merge r xs ys).Perm (xs ++ ys) := by
  fun_induction merge r xs ys with
  | case1 l => simp
  | case2 l _ => simp
  | case3 a as b bs _ ih => simpa using ih.cons a
  | case4 a as b bs _ ih => exact (ih.cons b).trans List.perm_middle.symm

/-- Membership in `merge r xs ys`. -/
theorem mem_merge {xs ys : List α} {x : α} :
    x ∈ merge r xs ys ↔ x ∈ xs ∨ x ∈ ys := by
  rw [(merge_perm r xs ys).mem_iff, List.mem_append]

/-- Merging two `r`-sorted lists yields an `r`-sorted list, provided `r` is total and
transitive. -/
theorem pairwise_merge (htot : ∀ a b : α, r a b ∨ r b a)
    (htrans : ∀ a b c : α, r a b → r b c → r a c) :
    ∀ xs ys : List α, List.Pairwise r xs → List.Pairwise r ys →
      List.Pairwise r (merge r xs ys) := by
  intro xs ys
  fun_induction merge r xs ys with
  | case1 l => intro _ h; exact h
  | case2 l _ => intro h1 _; exact h1
  | case3 a as b bs hab ih =>
      intro h1 h2
      rw [List.pairwise_cons]
      rw [List.pairwise_cons] at h1
      refine ⟨?_, ih h1.2 h2⟩
      intro x hx
      rcases (mem_merge r).1 hx with hx | hx
      · exact h1.1 x hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact hab
        · exact htrans _ _ _ hab ((List.pairwise_cons.1 h2).1 x hx)
  | case4 a as b bs hab ih =>
      intro h1 h2
      rw [List.pairwise_cons]
      have hba : r b a := (htot a b).resolve_left hab
      rw [List.pairwise_cons] at h2
      refine ⟨?_, ih h1 h2.2⟩
      intro x hx
      rcases (mem_merge r).1 hx with hx | hx
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact hba
        · exact htrans _ _ _ hba ((List.pairwise_cons.1 h1).1 x hx)
      · exact h2.1 x hx

/-! ### Correctness of `mergeSort` -/

/-- `mergeSort r l` is a permutation of `l`. -/
theorem mergeSort_perm (l : List α) : (mergeSort r l).Perm l := by
  fun_induction mergeSort r l with
  | case1 => exact List.Perm.refl _
  | case2 a => exact List.Perm.refl _
  | case3 a b t ih1 ih2 =>
      refine (merge_perm r _ _).trans ?_
      refine (ih1.append ih2).trans ?_
      rw [List.take_append_drop]

/-- `mergeSort r l` is `r`-sorted, provided `r` is total and transitive. -/
theorem pairwise_mergeSort (htot : ∀ a b : α, r a b ∨ r b a)
    (htrans : ∀ a b c : α, r a b → r b c → r a c) (l : List α) :
    List.Pairwise r (mergeSort r l) := by
  fun_induction mergeSort r l with
  | case1 => exact List.Pairwise.nil
  | case2 a => simp
  | case3 a b t ih1 ih2 =>
      exact pairwise_merge r htot htrans _ _ ih1 ih2

/-- **Mergesort is correct.**  For a total, transitive relation `r`, `mergeSort r l`
is a sorted (`List.Pairwise r`) permutation of the input list `l`. -/
theorem mergesort_correct (htot : ∀ a b : α, r a b ∨ r b a)
    (htrans : ∀ a b c : α, r a b → r b c → r a c) (l : List α) :
    List.Pairwise r (mergeSort r l) ∧ (mergeSort r l).Perm l :=
  ⟨pairwise_mergeSort r htot htrans l, mergeSort_perm r l⟩

end CS

