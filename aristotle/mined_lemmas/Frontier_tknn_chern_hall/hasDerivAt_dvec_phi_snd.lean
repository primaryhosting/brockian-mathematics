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

theorem hasDerivAt_dvec_phi_snd (θ φ : ℝ) :
    HasDerivAt (fun p : ℝ => (dvec θ p).2.1) (dPhi θ φ).2.1 φ := by
  have h : HasDerivAt (fun p : ℝ => sin θ * sin p) (sin θ * cos φ) φ :=
    (Real.hasDerivAt_sin φ).const_mul (sin θ)
  simpa [dvec, dPhi] using h

/-- `dPhi` is indeed the partial derivative of `dvec` with respect to `φ`
(third component). -/
