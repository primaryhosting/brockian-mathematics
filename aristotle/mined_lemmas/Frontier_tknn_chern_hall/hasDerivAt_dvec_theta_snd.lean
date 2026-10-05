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

theorem hasDerivAt_dvec_theta_snd (θ φ : ℝ) :
    HasDerivAt (fun t : ℝ => (dvec t φ).2.1) (dTheta θ φ).2.1 θ :=
  (Real.hasDerivAt_sin θ).mul_const _

/-- `dTheta` is indeed the partial derivative of `dvec` with respect to `θ`
(third component). -/
