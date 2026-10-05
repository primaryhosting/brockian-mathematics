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

noncomputable def laplacian (f : Vec → ℝ) (x : Vec) : ℝ :=
  ∑ j, partialDeriv (partialDeriv f j) j x

/-- The divergence `∇ · v = ∑ᵢ ∂ᵢ vᵢ` of a vector field on `ℝ³`. -/
