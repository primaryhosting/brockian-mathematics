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

import Mathlib

/-!
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped InnerProductSpace

namespace QPhys

variable {ι : Type*} [Fintype ι] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Expansion of `‖ψ‖²` in the coefficients of `ψ` with respect to an orthonormal basis
(Parseval's identity for a finite orthonormal basis). -/

theorem variational_bound (b : OrthonormalBasis ι ℂ V) (H : V →ₗ[ℂ] V) (Ev : ι → ℝ) (E0 : ℝ)
    (hH : ∀ i, H (b i) = (Ev i : ℂ) • b i) (hE0 : ∀ i, E0 ≤ Ev i)
    (ψ : V) (hψ : ψ ≠ 0) :
    E0 ≤ (inner ℂ ψ (H ψ)).re / (inner ℂ ψ ψ).re := by
  have hnorm : (0 : ℝ) < ‖ψ‖ ^ 2 := by positivity
  have hden : (inner ℂ ψ ψ).re = ‖ψ‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  rw [hden, le_div_iff₀ hnorm, re_inner_eq_sum_eigenvalues b H Ev hH ψ,
    norm_sq_eq_sum_repr_sq b ψ, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_right (hE0 i) (by positivity)

end QPhys

