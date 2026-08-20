/-
# Bcs Gap Binding
Category: Frontier Physics
Target: Frontier.bcs_gap_binding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

open Real intervalIntegral

/-- The antiderivative of the BCS kernel `ξ ↦ (√(ξ² + Δ²))⁻¹` is `ξ ↦ arsinh (ξ / Δ)`. -/
lemma hasDerivAt_arsinh_div (Δ : ℝ) (hΔ : 0 < Δ) (ξ : ℝ) :
    HasDerivAt (fun x : ℝ => Real.arsinh (x / Δ)) (Real.sqrt (ξ ^ 2 + Δ ^ 2))⁻¹ ξ := by
  have hbase : HasDerivAt (fun x : ℝ => x / Δ) (1 / Δ) ξ := by
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id ξ).mul_const Δ⁻¹
  have h := hbase.arsinh
  have h1 : 1 + (ξ / Δ) ^ 2 = (ξ ^ 2 + Δ ^ 2) / Δ ^ 2 := by
    field_simp; ring
  have hsq : Real.sqrt (1 + (ξ / Δ) ^ 2) = Real.sqrt (ξ ^ 2 + Δ ^ 2) / Δ := by
    rw [h1, Real.sqrt_div (by positivity), Real.sqrt_sq hΔ.le]
  have hpos : 0 < Real.sqrt (ξ ^ 2 + Δ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have key : (Real.sqrt (1 + (ξ / Δ) ^ 2))⁻¹ • (1 / Δ) = (Real.sqrt (ξ ^ 2 + Δ ^ 2))⁻¹ := by
    rw [hsq, smul_eq_mul]
    field_simp
  rw [key] at h
  exact h

/-- **Key intermediate lemma.** For a positive gap `Δ`, the BCS integral over the energy shell
`[0, ω]` evaluates in closed form:
`∫₀^ω dξ / √(ξ² + Δ²) = arsinh (ω / Δ)`. -/
lemma bcs_integral_eq_arsinh (Δ ω : ℝ) (hΔ : 0 < Δ) :
    (∫ ξ in (0:ℝ)..ω, (Real.sqrt (ξ ^ 2 + Δ ^ 2))⁻¹) = Real.arsinh (ω / Δ) := by
  have hcont : Continuous fun ξ : ℝ => (Real.sqrt (ξ ^ 2 + Δ ^ 2))⁻¹ := by
    apply Continuous.inv₀
    · exact (Real.continuous_sqrt.comp (by continuity))
    · intro ξ
      exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => Real.arsinh (x / Δ))
    (f' := fun x : ℝ => (Real.sqrt (x ^ 2 + Δ ^ 2))⁻¹)
    (fun x _ => hasDerivAt_arsinh_div Δ hΔ x)
    (hcont.intervalIntegrable 0 ω)
  simpa using this

/-- **BCS gap equation: existence of a nonzero gap for any attractive coupling.**

For every attractive coupling strength `g > 0` and every positive energy cutoff `ω`, the BCS
gap equation
`1 = g ∫₀^ω dξ / √(ξ² + Δ²)`
admits a strictly positive solution `Δ` (Cooper pairing): explicitly `Δ = ω / sinh (1/g)`.
Thus arbitrarily weak attraction still binds a pair. -/
theorem bcs_gap_binding (g ω : ℝ) (hg : 0 < g) (hω : 0 < ω) :
    ∃ Δ : ℝ, 0 < Δ ∧ g * (∫ ξ in (0:ℝ)..ω, (Real.sqrt (ξ ^ 2 + Δ ^ 2))⁻¹) = 1 := by
  have hsinh : 0 < Real.sinh (1 / g) := Real.sinh_pos_iff.mpr (one_div_pos.mpr hg)
  refine ⟨ω / Real.sinh (1 / g), by positivity, ?_⟩
  rw [bcs_integral_eq_arsinh _ _ (by positivity)]
  have : ω / (ω / Real.sinh (1 / g)) = Real.sinh (1 / g) := by
    field_simp
  rw [this, Real.arsinh_sinh]
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

