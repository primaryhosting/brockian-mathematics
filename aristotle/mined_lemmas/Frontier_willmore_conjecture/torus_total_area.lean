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

theorem torus_total_area (hr : 0 < r) (hRr : r < R) :
    (∫ _φ in (0 : ℝ)..(2 * π), ∫ θ in (0 : ℝ)..(2 * π), torusAreaElement R r θ)
      = 4 * π ^ 2 * R * r := by
  have hinner : (∫ θ in (0 : ℝ)..(2 * π), torusAreaElement R r θ) = 2 * π * (r * R) := by
    unfold torusAreaElement
    have hc2 : Continuous fun θ : ℝ => r ^ 2 * Real.cos θ :=
      continuous_const.mul Real.continuous_cos
    rw [intervalIntegral.integral_congr
        (g := fun θ => r * R + r ^ 2 * Real.cos θ) (fun θ _ => by ring),
      intervalIntegral.integral_add _root_.intervalIntegrable_const
        (hc2.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_cos, intervalIntegral.integral_const]
    simp [Real.sin_two_pi]
  rw [hinner, intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]
  ring

/-- **Gauss–Bonnet check**: the total Gauss curvature of the torus of revolution vanishes,
consistent with Euler characteristic `0`, i.e. genus `1`. -/
