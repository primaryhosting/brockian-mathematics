import Mathlib

/-!
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QPhys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A linear operator on a complex inner product space is *Hermitian* if it is symmetric
with respect to the inner product: `⟪T x, y⟫ = ⟪x, T y⟫` for all `x`, `y`. -/
def IsHermitian (T : E →ₗ[ℂ] E) : Prop :=
  ∀ x y : E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ

/-- `μ` is an eigenvalue of `T` if there is a nonzero vector `v` with `T v = μ • v`. -/
def HasEigenvalue (T : E →ₗ[ℂ] E) (μ : ℂ) : Prop :=
  ∃ v : E, v ≠ 0 ∧ T v = μ • v

/-- Key intermediate lemma: for a Hermitian operator `T` and an eigenvector `v` with
eigenvalue `μ`, the two ways of evaluating `⟪T v, v⟫` give
`conj μ * ⟪v, v⟫ = μ * ⟪v, v⟫`. -/
theorem conj_mul_inner_self_eq (T : E →ₗ[ℂ] E) (hT : IsHermitian T) {μ : ℂ} {v : E}
    (hv : T v = μ • v) :
    (starRingEnd ℂ) μ * ⟪v, v⟫_ℂ = μ * ⟪v, v⟫_ℂ := by
  have h := hT v v
  rw [hv] at h
  rwa [inner_smul_left, inner_smul_right] at h

/-- **Every eigenvalue of a Hermitian operator is real.** -/
theorem hermitian_real_spectrum (T : E →ₗ[ℂ] E) (hT : IsHermitian T) {μ : ℂ}
    (hμ : HasEigenvalue T μ) : ∃ r : ℝ, μ = (r : ℂ) := by
  obtain ⟨v, hv0, hv⟩ := hμ
  have hinner : ⟪v, v⟫_ℂ ≠ 0 := fun h => hv0 (inner_self_eq_zero.mp h)
  have h := conj_mul_inner_self_eq T hT hv
  have hconj : (starRingEnd ℂ) μ = μ := mul_right_cancel₀ hinner h
  exact ⟨μ.re, (Complex.conj_eq_iff_re.mp hconj).symm⟩

/-- Equivalent formulation: the eigenvalue equals its own complex conjugate. -/
theorem hermitian_eigenvalue_conj_eq_self (T : E →ₗ[ℂ] E) (hT : IsHermitian T) {μ : ℂ}
    (hμ : HasEigenvalue T μ) : (starRingEnd ℂ) μ = μ := by
  obtain ⟨r, hr⟩ := hermitian_real_spectrum T hT hμ
  simp [hr]

end QPhys

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

