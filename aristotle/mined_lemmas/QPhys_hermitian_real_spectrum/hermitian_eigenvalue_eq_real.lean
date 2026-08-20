/-
# Hermitian Real Spectrum
Category: Quantum Physics
Target: QPhys.hermitian_real_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open Module.End

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Every eigenvalue of a Hermitian operator is real.**

If `T` is a Hermitian (symmetric / self-adjoint) linear operator on a complex inner product
space `E` and `μ : ℂ` is an eigenvalue of `T`, then `μ` is real, i.e. `μ.im = 0`.

The key input is Mathlib's `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`. -/

theorem hermitian_eigenvalue_eq_real {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {μ : ℂ}
    (hμ : HasEigenvalue T μ) : ∃ r : ℝ, μ = (r : ℂ) :=
  ⟨μ.re, (Complex.conj_eq_iff_re.mp (hT.conj_eigenvalue_eq_self hμ)).symm⟩

/-- Matrix form: every eigenvalue of a Hermitian matrix is real. -/
