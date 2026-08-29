import Mathlib
/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Frontier

/-- The Berry flux of a band: the integral of the Berry curvature `F` over the
Brillouin torus `[0, 2π] × [0, 2π]`. -/

theorem chernNumber_of_berryFlux {F : ℝ → ℝ → ℝ} {n : ℤ}
    (hF : berryFlux F = 2 * Real.pi * n) : chernNumber F = (n : ℝ) := by
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := by positivity
  rw [chernNumber, hF, mul_div_assoc]
  field_simp

/-- The Berry curvature of the model band used as the base case: a smooth,
`2π`-periodic curvature on the Brillouin torus carrying one flux quantum. -/
