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

lemma partialDeriv_linear_pressure (c : Vec) (i : Fin 3) (x : Vec) :
    partialDeriv (fun y : Vec => -∑ k, c k * y k) i x = -c i := by
  have h : (fun y : Vec => -∑ k, c k * y k)
      = fun y => (-(∑ k, c k • (ContinuousLinearMap.proj k : Vec →L[ℝ] ℝ))) y := by
    funext y; simp
  rw [partialDeriv, h, ContinuousLinearMap.fderiv]
  simp [Pi.single_apply, Finset.sum_ite_eq']

/-- Sanity check on the definitions: the `j`-th partial derivative of the `i`-th coordinate
function is `1` if `i = j` and `0` otherwise. -/
