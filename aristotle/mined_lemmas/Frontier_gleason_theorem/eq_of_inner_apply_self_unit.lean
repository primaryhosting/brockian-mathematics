import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

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

namespace Frontier

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A *frame function of weight one*, Gleason's formulation of a quantum measure:
a function on the unit sphere which is nonnegative and whose values sum to `1`
over every orthonormal basis. -/
structure IsFrameFunction (f : H → ℝ) : Prop where
  nonneg : ∀ x : H, ‖x‖ = 1 → 0 ≤ f x
  sum_eq_one : ∀ b : OrthonormalBasis (Fin (Module.finrank ℂ H)) ℂ H, ∑ i, f (b i) = 1

/-- A density operator: a positive (hence self-adjoint) operator of trace one. -/

theorem eq_of_inner_apply_self_unit (S T : H →L[ℂ] H)
    (h : ∀ x : H, ‖x‖ = 1 → ⟪S x, x⟫_ℂ = ⟪T x, x⟫_ℂ) : S = T := by
  apply ContinuousLinearMap.coe_injective
  rw [← ext_inner_map]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hc : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    set u : H := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu_def
    have hu : ‖u‖ = 1 := by simp [hu_def, norm_smul, inv_mul_cancel₀ hc]
    have hxu : ((‖x‖ : ℝ) : ℂ) • u = x := by
      rw [hu_def, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hc]
      simp
    show ⟪S x, x⟫_ℂ = ⟪T x, x⟫_ℂ
    rw [← hxu, inner_apply_self_smul S ‖x‖ u, inner_apply_self_smul T ‖x‖ u, h u hu]

end Auxiliary

/-- If a quantum measure is the quadratic form of an operator `T`, then the values of that
quadratic form are nonnegative reals. -/
