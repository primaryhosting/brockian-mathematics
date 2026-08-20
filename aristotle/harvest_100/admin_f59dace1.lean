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

/-- **Hermitian operators have real spectrum.**

If `T` is a Hermitian (symmetric / self-adjoint) operator on a complex inner product space,
i.e. `⟪T x, y⟫ = ⟪x, T y⟫` for all `x y`, then every eigenvalue `μ` of `T` is real:
its imaginary part vanishes, and it equals the coercion of a real number.

The key ingredient is `LinearMap.IsSymmetric.conj_eigenvalue_eq_self` from Mathlib,
which states that `conj μ = μ` for an eigenvalue `μ` of a symmetric operator. -/
theorem hermitian_real_spectrum {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    {mu : ℂ} (hmu : HasEigenvalue T mu) :
    mu.im = 0 ∧ ∃ r : ℝ, mu = (r : ℂ) := by
  have h : (starRingEnd ℂ) mu = mu := hT.conj_eigenvalue_eq_self hmu
  have him : mu.im = 0 := by
    have h2 := congrArg Complex.im h
    simp only [Complex.conj_im] at h2
    linarith
  exact ⟨him, mu.re, by apply Complex.ext <;> simp [him]⟩

/-- Variant for a self-adjoint continuous operator on a complex Hilbert space:
every eigenvalue is real. -/
theorem hermitian_real_spectrum' [CompleteSpace E] {T : E →L[ℂ] E} (hT : IsSelfAdjoint T)
    {mu : ℂ} (hmu : HasEigenvalue (T : E →ₗ[ℂ] E) mu) :
    ∃ r : ℝ, mu = (r : ℂ) :=
  (hermitian_real_spectrum (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) hmu).2

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

