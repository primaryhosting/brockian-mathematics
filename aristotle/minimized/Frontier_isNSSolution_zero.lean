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

noncomputable def pd (i : Fin 3) (f : Vec → ℝ) (x : Vec) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-- The divergence of a vector field on `ℝ³`. -/

noncomputable def divergence (v : Vec → Vec) (x : Vec) : ℝ :=
  ∑ i, pd i (fun y => v y i) x

/-- The `i`-th component of the (spatial) Laplacian of a time dependent vector field. -/

@[simp] lemma pd_zero (i : Fin 3) (x : Vec) : pd i (fun _ : Vec => (0 : ℝ)) x = 0 := by
  simp [pd]
