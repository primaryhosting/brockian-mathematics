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

theorem hasDerivAt_dvec_phi_thd (θ φ : ℝ) :
    HasDerivAt (fun p : ℝ => (dvec θ p).2.2) (dPhi θ φ).2.2 φ := by
  simpa [dvec, dPhi] using (hasDerivAt_const φ (cos θ))

/-- The (unnormalised) Berry curvature density `d̂ · (∂_θ d̂ × ∂_φ d̂)` of the model. -/
