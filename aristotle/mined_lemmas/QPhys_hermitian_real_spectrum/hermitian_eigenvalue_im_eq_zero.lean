/-
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open Module.End

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Every eigenvalue of a Hermitian operator is real.**

If `T : E →ₗ[ℂ] E` is Hermitian (symmetric/self-adjoint, i.e. `⟪T x, y⟫ = ⟪x, T y⟫`)
and `μ : ℂ` is an eigenvalue of `T`, then `μ` is real: it equals the coercion of a
real number (equivalently, its imaginary part vanishes).

The core computation is Mathlib's `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`,
which gives `conj μ = μ`. -/

theorem hermitian_eigenvalue_im_eq_zero {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {μ : ℂ}
    (hμ : HasEigenvalue T μ) : μ.im = 0 := by
  obtain ⟨r, rfl⟩ := hermitian_real_spectrum hT hμ
  simp

/-- Continuous-operator version: every eigenvalue of a self-adjoint bounded operator
on a complex inner product space is real. -/
