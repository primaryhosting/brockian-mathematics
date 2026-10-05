/-
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open ContDiff

namespace Frontier

/-- The physical space `ℝ³`, modelled as `Fin 3 → ℝ`. -/
abbrev Vec := Fin 3 → ℝ

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/

noncomputable def partialDeriv (f : Vec → ℝ) (i : Fin 3) (x : Vec) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

/-- The Laplacian `Δf = ∑ⱼ ∂ⱼ∂ⱼ f` of a scalar field on `ℝ³`. -/
