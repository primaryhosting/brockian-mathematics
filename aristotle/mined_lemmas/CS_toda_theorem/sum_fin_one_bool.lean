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
Gap functions (differences of witness counts) and their closure properties.
-/
import RequestProject.Toda.Framework

namespace CS

open scoped BigOperators

/-! ### Splitting witnesses -/


theorem sum_fin_one_bool {M : Type*} [AddCommMonoid M] (F : (Fin 1 → Bool) → M) :
    ∑ y : Fin 1 → Bool, F y = F (fun _ => false) + F (fun _ => true) := by
  rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) Bool).symm F]
  rw [Fintype.sum_bool]
  have e : ∀ b : Bool, ((Equiv.funUnique (Fin 1) Bool).symm b) = (fun _ => b : Fin 1 → Bool) :=
    fun b => funext fun _ => rfl
  rw [e, e, add_comm]

/-- The sum of two gap functions with the *same* witness length; one extra bit of
witness selects which of the two is used. -/
