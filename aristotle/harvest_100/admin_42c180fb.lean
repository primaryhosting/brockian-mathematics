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
theorem hermitian_real_spectrum {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {μ : ℂ}
    (hμ : HasEigenvalue T μ) : μ.im = 0 :=
  Complex.conj_eq_iff_im.mp (hT.conj_eigenvalue_eq_self hμ)

/-- Restatement: an eigenvalue of a Hermitian operator equals (the coercion of) a real number. -/
theorem hermitian_eigenvalue_eq_real {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {μ : ℂ}
    (hμ : HasEigenvalue T μ) : ∃ r : ℝ, μ = (r : ℂ) :=
  ⟨μ.re, (Complex.conj_eq_iff_re.mp (hT.conj_eigenvalue_eq_self hμ)).symm⟩

/-- Matrix form: every eigenvalue of a Hermitian matrix is real. -/
theorem hermitian_matrix_real_spectrum {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) {μ : ℂ} (hμ : μ ∈ spectrum ℂ A) :
    μ.im = 0 := by
  rw [hA.spectrum_eq_image_range] at hμ
  obtain ⟨r, -, rfl⟩ := hμ
  simp

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

