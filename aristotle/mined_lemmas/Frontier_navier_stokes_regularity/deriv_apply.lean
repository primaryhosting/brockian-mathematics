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

lemma deriv_apply (ha : Differentiable ℝ a) (i : Fin 3) (t : ℝ) :
    deriv (fun s => a s i) t = deriv a t i :=
  ((hasDerivAt_pi.1 (ha t).hasDerivAt) i).deriv

/-- Partial derivatives of a spatially constant field vanish. -/
