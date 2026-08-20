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

namespace QPhys

local notation "⟪" x ", " y "⟫" => inner ℂ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An operator `A` on a complex inner product space is *symmetric* (formally self-adjoint)
when `⟪A x, y⟫ = ⟪x, A y⟫` for all `x, y`. -/

noncomputable def expect (A : E →ₗ[ℂ] E) (ψ : E) : ℝ := (⟪ψ, A ψ⟫).re

/-- The standard deviation (uncertainty) `Δ A = ‖(A - ⟨A⟩) ψ‖` of the observable `A`
in the state `ψ`. -/
