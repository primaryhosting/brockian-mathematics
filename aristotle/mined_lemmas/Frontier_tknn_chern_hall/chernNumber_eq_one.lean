/-
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real

namespace Frontier

/-! ## Vector algebra in `ℝ³`

We model `ℝ³` as `ℝ × ℝ × ℝ` and use the standard dot and cross products. -/

/-- The cross product of two vectors in `ℝ³`. -/

theorem chernNumber_eq_one : chernNumber = 1 := by
  have key : ∀ θ : ℝ, (∫ φ in (0 : ℝ)..(2 * π), berryCurvature θ φ) = 2 * π * sin θ := by
    intro θ
    simp [berryCurvature_eq, mul_comm]
  simp only [chernNumber, key]
  rw [intervalIntegral.integral_const_mul, integral_sin]
  simp only [Real.cos_zero, Real.cos_pi]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- The zero-temperature Hall conductance of the filled band, as given by the Kubo formula:
the Chern number times the conductance quantum `e²/h`. -/
