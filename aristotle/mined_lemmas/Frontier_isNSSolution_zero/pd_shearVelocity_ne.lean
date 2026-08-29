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

lemma pd_shearVelocity_ne (nu k t : ℝ) (i : Fin 3) {m : Fin 3} (hm : m ≠ 0) (x : Vec) :
    pd i (fun y => shearVelocity nu k t y m) x = 0 := by
  have : (fun y => shearVelocity nu k t y m) = fun _ : Vec => (0 : ℝ) :=
    funext fun y => shearVelocity_apply_ne nu k t y hm
  rw [this, pd_zero]

/-- The decaying shear flow is incompressible. -/
