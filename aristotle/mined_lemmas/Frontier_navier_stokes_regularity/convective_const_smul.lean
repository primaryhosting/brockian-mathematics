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

theorem convective_const_smul (c : ℝ) {v : Vec → Vec} (hv : Differentiable ℝ v) (x : Vec) :
    convective (fun y => c • v y) x = (c * c) • convective v x := by
  unfold convective
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [partialD_const_smul i c hv x]
  show (c * v x i) • c • partialD i v x = (c * c) • v x i • partialD i v x
  rw [smul_smul, smul_smul]
  ring_nf

