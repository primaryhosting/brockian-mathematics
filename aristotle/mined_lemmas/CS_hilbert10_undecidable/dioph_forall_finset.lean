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

/-
The moduli `1 + (i+1)q` used to code finite sequences, and the Chinese remainder theorem
for them.
-/
import RequestProject.H10.Arith

open Dioph Finset

namespace H10

/-- The `i`-th modulus of the Chinese remainder coding with parameter `q`. -/

theorem dioph_forall_finset {β : Type} {S : β → Set (α → ℕ)} (t : Finset β)
    (h : ∀ j, Dioph (S j)) : Dioph {v | ∀ j ∈ t, v ∈ S j} := by
  classical
  induction t using Finset.induction with
  | empty =>
      have huniv : Dioph (Set.univ : Set (α → ℕ)) :=
        Dioph.of_no_dummies _ 0 (fun v => ⟨fun _ => Poly.zero_apply v, fun _ => trivial⟩)
      exact Dioph.ext huniv (fun v => by simp)
  | insert a t ha ih =>
      refine Dioph.ext (Dioph.inter (h a) ih) fun v => ?_
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩ j (rfl | hj)
        · exact h1
        · exact h2 j hj
      · intro H
        exact ⟨H a (Or.inl rfl), fun j hj => H j (Or.inr hj)⟩

