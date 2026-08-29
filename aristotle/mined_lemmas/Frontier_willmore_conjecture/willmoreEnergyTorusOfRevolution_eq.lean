import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands of a
file, so the module documentation block above is placed immediately after `import Mathlib`.
-/

open Real Set MeasureTheory intervalIntegral

namespace Frontier

/-! ## The torus of revolution and its Willmore energy

For `0 < r < R`, the torus of revolution `T R r ⊆ ℝ³` obtained by revolving the circle of
radius `r` centred at distance `R` from the axis is parametrised by

  `(θ, φ) ↦ ((R + r cos θ) cos φ, (R + r cos θ) sin φ, r sin θ)`,  `θ, φ ∈ [0, 2π]`.

Its two principal curvatures are `1 / r` (along the meridian circle) and
`cos θ / (R + r cos θ)` (along the parallel circle), and its area element is
`r (R + r cos θ) dθ dφ`.  These classical formulas are taken as the definitions below;
the Willmore energy `∫ H² dA` is then the honest double integral of the square of the mean
curvature against the area element.
-/

/-- The principal curvature `k₁ = 1/r` of the torus of revolution, along the meridian
circle of radius `r`. -/

theorem willmoreEnergyTorusOfRevolution_eq (hr : 0 < r) (hRr : r < R) :
    willmoreEnergyTorusOfRevolution R r = π ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2)) := by
  have hs : 0 < R ^ 2 - r ^ 2 := by nlinarith
  have hsq : 0 < Real.sqrt (R ^ 2 - r ^ 2) := Real.sqrt_pos.mpr hs
  have hcont := continuous_inv_add_mul_cos hr hRr
  have hcont2 : Continuous fun θ : ℝ => R ^ 2 / (4 * r) * (R + r * Real.cos θ)⁻¹ :=
    continuous_const.mul hcont
  have hinner : (∫ θ in (0 : ℝ)..(2 * π),
        (torusMeanCurvature R r θ) ^ 2 * torusAreaElement R r θ)
      = R ^ 2 / (4 * r) * (2 * π / Real.sqrt (R ^ 2 - r ^ 2)) := by
    rw [intervalIntegral.integral_congr
      (g := fun θ => Real.cos θ + R ^ 2 / (4 * r) * (R + r * Real.cos θ)⁻¹)
      (fun θ _ => willmore_integrand_eq hr hRr θ)]
    rw [intervalIntegral.integral_add (Real.continuous_cos.intervalIntegrable _ _)
      (hcont2.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const_mul, integral_cos, integral_inv_add_mul_cos hr hRr]
    simp
  rw [willmoreEnergyTorusOfRevolution, hinner, intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]
  field_simp
  ring

/-- The lower bound `2π²` for the closed-form energy, with the equality case. -/
