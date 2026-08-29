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

lemma pd_coord (i j : Fin 3) (g : ℝ → ℝ) (hg : Differentiable ℝ g) (x : Vec) :
    pd i (fun y => g (y j)) x = if i = j then deriv g (x j) else 0 := by
  have hp : HasFDerivAt (fun y : Vec => y j) (EuclideanSpace.proj j : Vec →L[ℝ] ℝ) x := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt (x := x)
  have h1 := (hg (x j)).hasDerivAt.hasFDerivAt.comp x hp
  simp only [Function.comp_def] at h1
  rw [pd, h1.fderiv]
  simp [EuclideanSpace.single_apply, eq_comm]

/-- The velocity field of the decaying shear flow
`u(t, x) = (e^{-ν k² t} sin (k x₂), 0, 0)`. -/
