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
General linear algebra helpers: quotients `b / a` of nested submodules and additivity
of their dimensions along chains.
-/
import Mathlib

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Math2

open Submodule

variable {k M N : Type*} [Field k] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The quotient `b / a` of two submodules (interesting when `a ≤ b`). -/
abbrev Qt (a b : Submodule k M) : Type _ := b ⧸ a.submoduleOf b

/-- `b / ⊥ ≃ b`. -/

lemma mem_Lspace_iff_of_ne {D : Divisor Place} {x : K} (hx : x ≠ 0) :
    x ∈ V.Lspace D ↔ 0 ≤ V.divisorOf x + D := by
  rw [mem_Lspace]
  constructor
  · intro h P
    have := h P
    rw [V.ord_of_ne P hx] at this
    have h2 : -(D P) ≤ V.v P x := by exact_mod_cast this
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_zero, Pi.zero_apply]
    rw [V.divisorOf_apply hx]
    omega
  · intro h P
    have := h P
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.coe_zero, Pi.zero_apply] at this
    rw [V.divisorOf_apply hx] at this
    rw [V.ord_of_ne P hx]
    exact_mod_cast (by omega : -(D P) ≤ V.v P x)

