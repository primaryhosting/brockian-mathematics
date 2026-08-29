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

lemma partialDeriv_coord (i j : Fin 3) (x : Vec) :
    partialDeriv (fun y : Vec => y i) j x = if i = j then 1 else 0 := by
  have h : (fun y : Vec => y i) = fun y => (ContinuousLinearMap.proj i : Vec →L[ℝ] ℝ) y := rfl
  rw [partialDeriv, h, ContinuousLinearMap.fderiv]
  simp [Pi.single_apply]

/-- Sanity check on the definitions: the divergence of the identity vector field is `3`. -/
