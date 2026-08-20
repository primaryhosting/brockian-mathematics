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
