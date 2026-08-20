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

set_option grind.warning false

namespace QPhys

/-- **Every eigenvalue of a Hermitian operator is real.**

`T` is an operator on a complex inner product space `E` which is Hermitian (symmetric):
`⟪T x, y⟫ = ⟪x, T y⟫` for all `x y`. If `v ≠ 0` is an eigenvector with eigenvalue `μ`,
then `μ` is real, i.e. `μ = (r : ℂ)` for some real `r`.

The key ingredient is Mathlib's `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`. -/
theorem hermitian_real_spectrum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {μ : ℂ} {v : E} (hv : v ≠ 0)
    (heigen : T v = μ • v) : ∃ r : ℝ, μ = (r : ℂ) := by
  have hvec : Module.End.HasEigenvector T μ v :=
    ⟨Module.End.mem_eigenspace_iff.mpr heigen, hv⟩
  have hconj : (starRingEnd ℂ) μ = μ :=
    hT.conj_eigenvalue_eq_self (Module.End.hasEigenvalue_of_hasEigenvector hvec)
  refine ⟨μ.re, ?_⟩
  have him : μ.im = 0 := by
    have := congrArg Complex.im hconj
    simp only [Complex.conj_im] at this
    linarith
  exact Complex.ext rfl (by simp [him])

end QPhys

