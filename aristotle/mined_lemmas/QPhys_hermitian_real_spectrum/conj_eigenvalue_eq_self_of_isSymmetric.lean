/-
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open scoped InnerProductSpace

/-- Key computation: if `T` is symmetric (Hermitian) and `T v = μ • v` with `v ≠ 0`,
then `conj μ = μ`. -/

theorem conj_eigenvalue_eq_self_of_isSymmetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →ₗ[ℂ] E} (hT : ∀ x y : E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    {μ : ℂ} {v : E} (hv : v ≠ 0) (hTv : T v = μ • v) :
    (starRingEnd ℂ) μ = μ := by
  have key : (starRingEnd ℂ) μ * ⟪v, v⟫_ℂ = μ * ⟪v, v⟫_ℂ := by
    have h := hT v v
    rw [hTv] at h
    rw [inner_smul_left, inner_smul_right] at h
    exact h
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := by
    simpa [inner_self_eq_zero] using hv
  exact mul_right_cancel₀ hvv key

/-- **Every eigenvalue of a Hermitian operator is real.**

If `T` is a Hermitian (symmetric) linear operator on a complex inner product space and
`μ` is an eigenvalue of `T` (i.e. `T v = μ • v` for some nonzero vector `v`), then `μ`
is a real number: it has zero imaginary part, and indeed equals the coercion of a real. -/
