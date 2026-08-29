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

theorem divergence_const_smul (c : ℝ) {v : Vec → Vec} (hv : Differentiable ℝ v) (x : Vec) :
    divergence (fun y => c • v y) x = c * divergence v x := by
  unfold divergence
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (fun y => (c • v y) i) = fun y => c • (v y i) := rfl
  rw [h1, partialD_const_smul i c (differentiable_coord hv i) x, smul_eq_mul]

