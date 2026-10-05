import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ContDiff BigOperators

namespace Frontier

/-- The physical space `ℝ³`, as the space of `3`-tuples of reals. -/
abbrev Vec : Type := Fin 3 → ℝ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `i`-th partial derivative of a (vector- or scalar-valued) field on `ℝ³`. -/

theorem differentiable_coord {v : Vec → Vec} (hv : Differentiable ℝ v) (i : Fin 3) :
    Differentiable ℝ (fun y => v y i) :=
  ((ContinuousLinearMap.proj i : Vec →L[ℝ] ℝ).differentiable).comp hv

