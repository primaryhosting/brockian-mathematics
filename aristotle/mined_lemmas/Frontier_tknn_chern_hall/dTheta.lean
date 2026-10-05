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

noncomputable def dTheta (θ φ : ℝ) : ℝ × ℝ × ℝ := (cos θ * cos φ, cos θ * sin φ, -sin θ)

/-- The candidate `φ`-derivative of `dvec`. -/
