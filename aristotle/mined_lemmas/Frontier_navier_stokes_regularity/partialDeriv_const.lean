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

@[simp] lemma partialDeriv_const (c : ℝ) (i : Fin 3) (x : Vec) :
    partialDeriv (fun _ : Vec => c) i x = 0 := by
  simp [partialDeriv]

/-- The Laplacian of a spatially constant field vanishes. -/
