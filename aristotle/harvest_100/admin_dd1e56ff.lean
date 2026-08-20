/-
# Bcs Gap Binding
Category: Frontier Physics
Target: Frontier.bcs_gap_binding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bcs Gap Binding
Category: Frontier Physics
Target: Frontier.bcs_gap_binding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open intervalIntegral MeasureTheory

/-- The integrand of the zero-temperature BCS gap equation,
`ξ ↦ 1 / √(ξ² + Δ²)`, has the antiderivative `ξ ↦ arsinh (ξ / Δ)`. -/
theorem hasDerivAt_arsinh_div (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) :
    HasDerivAt (fun ξ : ℝ => Real.arsinh (ξ / Δ)) (1 / Real.sqrt (x ^ 2 + Δ ^ 2)) x := by
  have hx : HasDerivAt (fun ξ : ℝ => ξ / Δ) (1 / Δ) x := by
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id x).mul_const Δ⁻¹
  have h := (Real.hasDerivAt_arsinh (x / Δ)).comp x hx
  have harg : 1 + (x / Δ) ^ 2 = (x ^ 2 + Δ ^ 2) / Δ ^ 2 := by
    field_simp; ring
  have hsq : Real.sqrt (1 + (x / Δ) ^ 2) = Real.sqrt (x ^ 2 + Δ ^ 2) / Δ := by
    rw [harg, Real.sqrt_div (by positivity), Real.sqrt_sq hΔ.le]
  have hpos : 0 < Real.sqrt (x ^ 2 + Δ ^ 2) := Real.sqrt_pos.2 (by positivity)
  convert h using 1
  rw [hsq]
  field_simp

/-- **Key lemma.** Evaluation of the zero-temperature BCS gap integral:
for a positive gap `Δ`, `∫_0^ω dξ / √(ξ² + Δ²) = arsinh (ω / Δ)`. -/
theorem bcs_gap_integral (Δ ω : ℝ) (hΔ : 0 < Δ) :
    ∫ ξ in (0:ℝ)..ω, 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2) = Real.arsinh (ω / Δ) := by
  have hcont : Continuous fun ξ : ℝ => 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2) := by
    apply Continuous.div continuous_const
    · exact (Real.continuous_sqrt.comp (by continuity))
    · intro ξ
      exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun ξ : ℝ => Real.arsinh (ξ / Δ))
    (f' := fun ξ : ℝ => 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2))
    (fun x _ => hasDerivAt_arsinh_div Δ hΔ x)
    (hcont.intervalIntegrable 0 ω)
  simpa using this

/-- **BCS gap binding (Cooper pairing).** For any attractive coupling `lam > 0` and any
positive Debye cutoff `ω`, the zero-temperature BCS gap equation
`lam * ∫_0^ω dξ / √(ξ² + Δ²) = 1` has a strictly positive solution `Δ`,
namely `Δ = ω / sinh (1 / lam)`. -/
theorem bcs_gap_binding (lam ω : ℝ) (hlam : 0 < lam) (hω : 0 < ω) :
    ∃ Δ : ℝ, 0 < Δ ∧ lam * ∫ ξ in (0:ℝ)..ω, 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2) = 1 := by
  have hs : 0 < Real.sinh (1 / lam) := Real.sinh_pos_iff.2 (by positivity)
  refine ⟨ω / Real.sinh (1 / lam), by positivity, ?_⟩
  rw [bcs_gap_integral _ _ (by positivity)]
  have harg : ω / (ω / Real.sinh (1 / lam)) = Real.sinh (1 / lam) := by
    field_simp
  rw [harg, Real.arsinh_sinh]
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

