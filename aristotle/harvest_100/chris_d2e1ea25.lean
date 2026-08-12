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

namespace Frontier

open Real MeasureTheory intervalIntegral

/-- The BCS pairing integral
`∫₀^ω dξ / √(ξ² + Δ²)`, i.e. the right-hand side of the BCS gap equation for a
constant density of states, energy cutoff `ω` and gap parameter `Δ`. -/
noncomputable def bcsGapIntegral (omega Delta : ℝ) : ℝ :=
  ∫ x in (0:ℝ)..omega, (Real.sqrt (x ^ 2 + Delta ^ 2))⁻¹

/-- The antiderivative `y ↦ arsinh (y / Δ)` of the BCS integrand. -/
lemma hasDerivAt_arsinh_div {Delta : ℝ} (hD : 0 < Delta) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.arsinh (y / Delta))
      (Real.sqrt (x ^ 2 + Delta ^ 2))⁻¹ x := by
  have h1 : HasDerivAt (fun y : ℝ => y / Delta) (1 / Delta) x := by
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id x).mul_const Delta⁻¹
  have h2 := (Real.hasDerivAt_arsinh (x / Delta)).comp x h1
  have hkey : Real.sqrt (1 + (x / Delta) ^ 2) = Real.sqrt (x ^ 2 + Delta ^ 2) / Delta := by
    rw [show (1 : ℝ) + (x / Delta) ^ 2 = (x ^ 2 + Delta ^ 2) / Delta ^ 2 by field_simp; ring,
      Real.sqrt_div (by positivity), Real.sqrt_sq hD.le]
  have hpos : 0 < Real.sqrt (x ^ 2 + Delta ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [hkey] at h2
  convert h2 using 1
  field_simp

lemma continuous_inv_sqrt_sq_add_sq {Delta : ℝ} (hD : 0 < Delta) :
    Continuous (fun x : ℝ => (Real.sqrt (x ^ 2 + Delta ^ 2))⁻¹) := by
  apply Continuous.inv₀
  · fun_prop
  · intro x; positivity

/-- Closed form of the BCS pairing integral: `∫₀^ω dξ/√(ξ²+Δ²) = arsinh (ω/Δ)`. -/
theorem bcsGapIntegral_eq_arsinh {omega Delta : ℝ} (hD : 0 < Delta) :
    bcsGapIntegral omega Delta = Real.arsinh (omega / Delta) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ => Real.arsinh (y / Delta))
    (f' := fun x : ℝ => (Real.sqrt (x ^ 2 + Delta ^ 2))⁻¹)
    (fun x _ => hasDerivAt_arsinh_div hD x)
    ((continuous_inv_sqrt_sq_add_sq hD).intervalIntegrable 0 omega)
  simpa [bcsGapIntegral] using h

/-- **Cooper pairing / BCS gap binding.**  For every attractive coupling `g > 0` and every
positive energy cutoff `omega`, the BCS gap equation
`1 = g * ∫₀^omega dξ / √(ξ² + Δ²)`
has a strictly positive (in particular nonzero) solution `Δ`, namely
`Δ = omega / sinh (1 / g)`. -/
theorem bcs_gap_binding {g omega : ℝ} (hg : 0 < g) (hw : 0 < omega) :
    ∃ Delta : ℝ, 0 < Delta ∧ g * bcsGapIntegral omega Delta = 1 := by
  have hs : 0 < Real.sinh (1 / g) := Mathlib.Meta.Positivity.sinh_pos_of_pos (by positivity)
  refine ⟨omega / Real.sinh (1 / g), by positivity, ?_⟩
  have hdiv : omega / (omega / Real.sinh (1 / g)) = Real.sinh (1 / g) := by
    field_simp
  rw [bcsGapIntegral_eq_arsinh (by positivity), hdiv, Real.arsinh_sinh]
  field_simp

/-- The BCS gap `Δ = ω / sinh (1/g)` is the *unique* positive solution of the gap equation. -/
theorem bcs_gap_binding_unique {g omega : ℝ} (hg : 0 < g) (hw : 0 < omega) :
    ∃! Delta : ℝ, 0 < Delta ∧ g * bcsGapIntegral omega Delta = 1 := by
  have hs : 0 < Real.sinh (1 / g) := Mathlib.Meta.Positivity.sinh_pos_of_pos (by positivity)
  refine ⟨omega / Real.sinh (1 / g), ⟨by positivity, ?_⟩, ?_⟩
  · have hdiv : omega / (omega / Real.sinh (1 / g)) = Real.sinh (1 / g) := by field_simp
    rw [bcsGapIntegral_eq_arsinh (by positivity), hdiv, Real.arsinh_sinh]
    field_simp
  · rintro D ⟨hD, hDeq⟩
    rw [bcsGapIntegral_eq_arsinh hD] at hDeq
    have h1 : Real.arsinh (omega / D) = 1 / g := by
      field_simp at hDeq ⊢; linarith [hDeq]
    have h2 : omega / D = Real.sinh (1 / g) := by
      rw [← h1, Real.sinh_arsinh]
    field_simp at h2 ⊢
    linarith [h2]

end Frontier

