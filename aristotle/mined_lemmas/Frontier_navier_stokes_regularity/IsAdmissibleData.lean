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

def IsAdmissibleData (u₀ : Vec → Vec) : Prop :=
  ContDiff ℝ ∞ u₀ ∧ HasCompactSupport u₀ ∧ ∀ x, divergence u₀ x = 0

/-- Existence of a globally defined smooth solution with bounded energy for the initial
datum `u₀` and viscosity `ν`. -/
