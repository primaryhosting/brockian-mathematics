/-
/-!
# Bcs Gap Binding
Category: Frontier Physics
Target: Frontier.bcs_gap_binding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

namespace Frontier

open Real intervalIntegral

/-- The BCS kernel `ξ ↦ 1 / √(ξ² + Δ²)` is continuous when `Δ ≠ 0`. -/
lemma continuous_bcs_kernel {Δ : ℝ} (hΔ : Δ ≠ 0) :
    Continuous (fun ξ : ℝ => 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2)) := by
  have hpos : ∀ ξ : ℝ, 0 < ξ ^ 2 + Δ ^ 2 := by
    intro ξ
    have h : 0 < Δ ^ 2 := by positivity
    nlinarith [sq_nonneg ξ]
  refine Continuous.div continuous_const
    (((continuous_pow 2).add continuous_const).sqrt) (fun ξ => ?_)
  exact ne_of_gt (Real.sqrt_pos.mpr (hpos ξ))

/-- The antiderivative: `ξ ↦ arsinh (ξ / Δ)` has derivative `1 / √(ξ² + Δ²)`. -/
lemma hasDerivAt_arsinh_div {Δ : ℝ} (hΔ : 0 < Δ) (ξ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.arsinh (x / Δ))
      (1 / Real.sqrt (ξ ^ 2 + Δ ^ 2)) ξ := by
  have h1 : HasDerivAt (fun x : ℝ => x / Δ) (1 / Δ) ξ := by
    simpa [div_eq_mul_inv] using (hasDerivAt_id ξ).mul_const Δ⁻¹
  have h2 := (Real.hasDerivAt_arsinh (ξ / Δ)).comp ξ h1
  have h3 : Real.sqrt (ξ ^ 2 + Δ ^ 2) = Real.sqrt (1 + (ξ / Δ) ^ 2) * Δ := by
    rw [show ξ ^ 2 + Δ ^ 2 = (1 + (ξ / Δ) ^ 2) * Δ ^ 2 by field_simp; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hΔ.le]
  have hspos : 0 < Real.sqrt (1 + (ξ / Δ) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hkey : (Real.sqrt (1 + (ξ / Δ) ^ 2))⁻¹ * Δ⁻¹
      = (Real.sqrt (ξ ^ 2 + Δ ^ 2))⁻¹ := by
    rw [h3]; field_simp
  simpa [Function.comp_def, one_div, hkey] using h2

/-- Evaluation of the BCS gap integral. -/
lemma bcs_integral_eq {Δ ω : ℝ} (hΔ : 0 < Δ) :
    (∫ ξ in (0:ℝ)..ω, 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2)) = Real.arsinh (ω / Δ) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => Real.arsinh (x / Δ))
    (f' := fun ξ : ℝ => 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2))
    (fun x _ => hasDerivAt_arsinh_div hΔ x)
    ((continuous_bcs_kernel hΔ.ne').intervalIntegrable 0 ω)
  simpa using h

/-- **BCS gap equation.**  For any attractive coupling `g > 0` and cutoff `ω > 0`
there is a strictly positive gap `Δ` solving `g ∫₀^ω dξ / √(ξ² + Δ²) = 1`. -/
theorem bcs_gap_binding (g ω : ℝ) (hg : 0 < g) (hω : 0 < ω) :
    ∃ Δ : ℝ, 0 < Δ ∧ g * ∫ ξ in (0:ℝ)..ω, 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2) = 1 := by
  have hs : 0 < Real.sinh (1 / g) := Mathlib.Meta.Positivity.sinh_pos_of_pos (by positivity)
  refine ⟨ω / Real.sinh (1 / g), by positivity, ?_⟩
  rw [bcs_integral_eq (by positivity)]
  rw [show ω / (ω / Real.sinh (1 / g)) = Real.sinh (1 / g) by
    field_simp]
  rw [Real.arsinh_sinh]
  field_simp

end Frontier

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

