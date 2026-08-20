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

theorem hermitian_real_spectrum_clm [CompleteSpace E] {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) {μ : ℂ}
    (hμ : HasEigenvalue (T : E →ₗ[ℂ] E) μ) : ∃ r : ℝ, μ = (r : ℂ) :=
  hermitian_real_spectrum (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) hμ

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

