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

theorem energy_rescale (v : ℝ → Vec → Vec) (ν t : ℝ) :
    energy (fun t x => ν • v (ν * t) x) t = ν ^ 2 * energy v (ν * t) := by
  unfold energy
  rw [← MeasureTheory.integral_const_mul]
  refine congrArg _ (funext fun x => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (ν * v (ν * t) x i) ^ 2 = ν ^ 2 * (v (ν * t) x i) ^ 2
  ring

/-- **Lean-checked reduction.** Global regularity for unit viscosity implies global
regularity for every positive viscosity. -/
