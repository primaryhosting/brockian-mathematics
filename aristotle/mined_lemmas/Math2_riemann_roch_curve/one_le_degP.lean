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

lemma one_le_degP (P : Place) : 1 ≤ V.degP P := by
  have := hfin P
  have h1 : (1 : K) ∈ V.Kge P 0 := by
    show ((0 : ℤ) : WithTop ℤ) ≤ V.ord P 1
    rw [V.ord_of_ne P one_ne_zero, V.v_one]
  have hne : Nontrivial (Qt (V.Kge P 1) (V.Kge P 0)) := by
    refine ⟨⟨Submodule.Quotient.mk ⟨1, h1⟩, 0, ?_⟩⟩
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    intro hmem
    have h2 : (1 : K) ∈ V.Kge P 1 := hmem
    have h3 : ((1 : ℤ) : WithTop ℤ) ≤ V.ord P 1 := h2
    rw [V.ord_of_ne P one_ne_zero, V.v_one] at h3
    have h4 : (1 : ℤ) ≤ 0 := WithTop.coe_le_coe.mp h3
    omega
  exact Module.finrank_pos

end PlaceData

end Math2

/-
Divisors, their degrees, the Riemann-Roch spaces `L(D)`, and the axioms defining
the function field of a smooth projective curve.
-/
import RequestProject.RR.Divisor

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Math2

/-- A divisor: a finitely supported integer combination of closed points. -/
abbrev Divisor (Place : Type*) := Place →₀ ℤ

namespace PlaceData

variable {k K Place : Type*} [Field k] [Field K] [Algebra k K] (V : PlaceData k K Place)

/-! ### Degree of a divisor -/

/-- The degree of a divisor. -/
