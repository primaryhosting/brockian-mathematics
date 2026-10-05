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

lemma integral_inv_add_mul_cos (hr : 0 < r) (hRr : r < R) :
    ∫ θ in (0 : ℝ)..(2 * π), (R + r * Real.cos θ)⁻¹ = 2 * π / Real.sqrt (R ^ 2 - r ^ 2) := by
  have hcont := continuous_inv_add_mul_cos hr hRr
  have hrefl : ∀ x : ℝ, (R + r * Real.cos (2 * π - x))⁻¹ = (R + r * Real.cos x)⁻¹ := by
    intro x
    rw [Real.cos_two_pi_sub]
  have h2 := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := π)
    (fun θ : ℝ => (R + r * Real.cos θ)⁻¹) (2 * π)
  simp only [hrefl] at h2
  rw [show 2 * π - π = π by ring, sub_zero] at h2
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (a := (0 : ℝ)) (b := π) (c := 2 * π) (μ := MeasureTheory.volume)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
  rw [← hadd, ← h2, integral_inv_add_mul_cos_zero_pi hr hRr]
  ring

end KeyIntegral

section ClosedForm

variable {R r : ℝ}

/-- **Willmore's closed formula**: the Willmore energy of the torus of revolution with
radii `R > r > 0` equals `π² R² / (r √(R² - r²))`. -/
