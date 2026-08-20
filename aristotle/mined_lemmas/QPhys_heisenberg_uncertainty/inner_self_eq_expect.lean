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

lemma inner_self_eq_expect {A : E →ₗ[ℂ] E} (hA : IsSymmetricOp A) (ψ : E) :
    ⟪ψ, A ψ⟫ = ((expect A ψ : ℝ) : ℂ) := by
  have h : (starRingEnd ℂ) (⟪ψ, A ψ⟫) = ⟪ψ, A ψ⟫ := by
    rw [inner_conj_symm]
    exact hA ψ ψ
  have := Complex.conj_eq_iff_im.mp h
  simp [expect, Complex.ext_iff, this]

/-- **Key algebraic step.** For symmetric `A`, `B` and real shifts `a`, `b`, the
anti-symmetric part of `⟪(A - a) ψ, (B - b) ψ⟫` is the expectation of the commutator. -/
