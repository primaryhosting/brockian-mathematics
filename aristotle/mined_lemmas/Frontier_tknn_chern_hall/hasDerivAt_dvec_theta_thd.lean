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

theorem hasDerivAt_dvec_theta_thd (θ φ : ℝ) :
    HasDerivAt (fun t : ℝ => (dvec t φ).2.2) (dTheta θ φ).2.2 θ :=
  Real.hasDerivAt_cos θ

/-- `dPhi` is indeed the partial derivative of `dvec` with respect to `φ`
(first component). -/
