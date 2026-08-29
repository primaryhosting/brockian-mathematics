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

theorem dvec_norm_sq (θ φ : ℝ) : dot3 (dvec θ φ) (dvec θ φ) = 1 := by
  simp only [dot3, dvec]
  linear_combination (sin θ ^ 2) * sin_sq_add_cos_sq φ + sin_sq_add_cos_sq θ

/-- `dTheta` is indeed the partial derivative of `dvec` with respect to `θ`
(first component). -/
