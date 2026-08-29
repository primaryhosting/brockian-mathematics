/-
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped BigOperators

/-- Physical space `ℝ³`. -/
abbrev Vec := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/

lemma pd_shearVelocity_zero (nu k t : ℝ) (i : Fin 3) (x : Vec) :
    pd i (fun y => shearVelocity nu k t y 0) x =
      if i = 1 then Real.exp (-(nu * k ^ 2) * t) * (k * Real.cos (k * x 1)) else 0 := by
  have h := pd_coord i 1 (fun s : ℝ => Real.exp (-(nu * k ^ 2) * t) * Real.sin (k * s))
    (differentiable_shear_profile _ _) x
  rw [deriv_shear_profile] at h
  simpa [shearVelocity_apply] using h

