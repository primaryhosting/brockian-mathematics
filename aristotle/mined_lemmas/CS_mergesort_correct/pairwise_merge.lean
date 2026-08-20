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
