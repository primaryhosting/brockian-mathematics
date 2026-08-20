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
