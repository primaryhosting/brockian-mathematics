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

/-- **Every eigenvalue of a Hermitian operator is real.**

`E` is a complex inner product space (the state space), `T : E →ₗ[ℂ] E` is a Hermitian
(symmetric) operator, i.e. `⟪T x, y⟫ = ⟪x, T y⟫` for all states `x`, `y`.  If `μ : ℂ` is an
eigenvalue of `T`, witnessed by a nonzero eigenvector `v` with `T v = μ • v`, then `μ` is real:
its imaginary part vanishes, so `μ = (μ.re : ℂ)`.

The proof is the standard one: `μ ⟪v, v⟫ = ⟪v, T v⟫ = ⟪T v, v⟫ = conj μ ⟪v, v⟫`, and
`⟪v, v⟫ ≠ 0` since `v ≠ 0`; hence `conj μ = μ`.  (Mathlib packages this argument as
`LinearMap.IsSymmetric.conj_eigenvalue_eq_self`.) -/
theorem hermitian_real_spectrum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : ∀ x y : E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (μ : ℂ) (v : E) (hv : v ≠ 0) (heig : T v = μ • v) :
    μ.im = 0 ∧ μ = (μ.re : ℂ) := by
  have hconj : (starRingEnd ℂ) μ = μ := by
    have hinner : (starRingEnd ℂ) μ * ⟪v, v⟫_ℂ = μ * ⟪v, v⟫_ℂ := by
      have h1 : ⟪T v, v⟫_ℂ = (starRingEnd ℂ) μ * ⟪v, v⟫_ℂ := by
        rw [heig, inner_smul_left]
      have h2 : ⟪v, T v⟫_ℂ = μ * ⟪v, v⟫_ℂ := by
        rw [heig, inner_smul_right]
      rw [← h1, ← h2, hT]
    have hvv : ⟪v, v⟫_ℂ ≠ 0 := by
      simpa [inner_self_eq_zero] using hv
    exact mul_right_cancel₀ hvv hinner
  exact ⟨Complex.conj_eq_iff_im.mp hconj, (Complex.conj_eq_iff_re.mp hconj).symm⟩

/-- The same statement in Mathlib's idiom: for a symmetric (Hermitian) operator `T` on a complex
inner product space, every eigenvalue of `T` is real.  This is a direct consequence of
`LinearMap.IsSymmetric.conj_eigenvalue_eq_self`. -/
theorem hermitian_real_spectrum_of_isSymmetric
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) {μ : ℂ} (hμ : Module.End.HasEigenvalue T μ) :
    μ.im = 0 :=
  Complex.conj_eq_iff_im.mp (hT.conj_eigenvalue_eq_self hμ)

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

