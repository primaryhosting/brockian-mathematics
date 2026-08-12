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

open scoped InnerProductSpace

namespace QPhys

/-- **Every eigenvalue of a Hermitian operator is real.**

`T` is a Hermitian (symmetric / self-adjoint) operator on a complex inner product space `E`,
expressed by `⟪T x, y⟫ = ⟪x, T y⟫` for all `x y`.  If `μ` is an eigenvalue of `T`, witnessed by
a nonzero eigenvector `v` with `T v = μ • v`, then `μ` is real, i.e. `μ = (r : ℂ)` for some
real number `r`. -/
theorem hermitian_real_spectrum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : ∀ x y : E, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ)
    (μ : ℂ) (v : E) (hv : v ≠ 0) (heig : T v = μ • v) :
    ∃ r : ℝ, μ = (r : ℂ) := by
  refine ⟨μ.re, ?_⟩
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hv
  have h := hT v v
  rw [heig, inner_smul_left, inner_smul_right] at h
  have hc : (starRingEnd ℂ) μ = μ := mul_right_cancel₀ hvv h
  have him := Complex.conj_eq_iff_im.mp hc
  exact Complex.ext rfl (by simp [him])

end QPhys

