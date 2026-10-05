import Mathlib

/-!
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Hermitian operators have real spectrum.**
If `A` is a Hermitian (symmetric) operator on a complex inner product space and
`v ≠ 0` is an eigenvector of `A` with eigenvalue `μ`, then `μ` is real:
it is fixed by complex conjugation and has vanishing imaginary part. -/
theorem hermitian_real_spectrum
    (A : E →ₗ[ℂ] E) (hA : ∀ x y : E, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (μ : ℂ) (v : E) (hv : v ≠ 0) (heig : A v = μ • v) :
    (starRingEnd ℂ) μ = μ ∧ μ.im = 0 := by
  have hnorm : (⟪v, v⟫_ℂ) ≠ 0 := by
    simpa [inner_self_eq_zero] using hv
  have key : (starRingEnd ℂ) μ * ⟪v, v⟫_ℂ = μ * ⟪v, v⟫_ℂ := by
    have h1 : ⟪A v, v⟫_ℂ = (starRingEnd ℂ) μ * ⟪v, v⟫_ℂ := by
      rw [heig, inner_smul_left]
    have h2 : ⟪v, A v⟫_ℂ = μ * ⟪v, v⟫_ℂ := by
      rw [heig, inner_smul_right]
    rw [← h1, ← h2, hA]
  have hconj : (starRingEnd ℂ) μ = μ := mul_right_cancel₀ hnorm key
  refine ⟨hconj, ?_⟩
  have him := congrArg Complex.im hconj
  simp only [Complex.conj_im] at him
  linarith

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

