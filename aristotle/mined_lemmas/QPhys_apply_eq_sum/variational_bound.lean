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

/-
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open scoped InnerProductSpace

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Expansion of `H ψ` in an orthonormal eigenbasis of `H`. -/

theorem variational_bound (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V) (mu : Fin n → ℝ)
    (hH : ∀ i, H (b i) = (mu i : ℂ) • b i) (E0 : ℝ) (hE0 : ∀ i, E0 ≤ mu i)
    (psi : V) (hpsi : psi ≠ 0) :
    E0 ≤ (⟪psi, H psi⟫_ℂ).re / (⟪psi, psi⟫_ℂ).re := by
  have hden : (⟪psi, psi⟫_ℂ).re = ‖psi‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) psi
  have hpos : 0 < (⟪psi, psi⟫_ℂ).re := by
    rw [hden]
    have : 0 < ‖psi‖ := norm_pos_iff.mpr hpsi
    positivity
  rw [le_div_iff₀ hpos, inner_apply_eq_sum b H mu hH psi, inner_self_eq_sum b psi]
  simp only [Complex.ofReal_re]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_right (hE0 i) (by positivity)

#print axioms QPhys.variational_bound

end QPhys

