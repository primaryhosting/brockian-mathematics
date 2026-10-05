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

lemma divergence_shearVelocity (nu k t : ℝ) (x : Vec) :
    divergence (shearVelocity nu k t) x = 0 := by
  have h0 : pd 0 (fun y => shearVelocity nu k t y 0) x = 0 := by
    rw [pd_shearVelocity_zero]; norm_num
  simp [divergence, Fin.sum_univ_three, h0,
    pd_shearVelocity_ne nu k t 1 (m := 1) (by decide),
    pd_shearVelocity_ne nu k t 2 (m := 2) (by decide)]

/-- The Laplacian of the first component of the shear velocity field. -/
