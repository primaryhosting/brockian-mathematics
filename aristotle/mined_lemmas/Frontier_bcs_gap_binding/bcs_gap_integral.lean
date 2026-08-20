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
