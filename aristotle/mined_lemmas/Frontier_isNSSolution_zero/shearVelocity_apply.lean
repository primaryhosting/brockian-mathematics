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

lemma shearVelocity_apply (nu k t : ℝ) (x : Vec) (i : Fin 3) :
    shearVelocity nu k t x i =
      if i = 0 then Real.exp (-(nu * k ^ 2) * t) * Real.sin (k * x 1) else 0 := by
  simp [shearVelocity, EuclideanSpace.single_apply]

