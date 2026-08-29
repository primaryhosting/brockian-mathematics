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

theorem laplacian_const_smul (c : ℝ) {f : Vec → E} (hf : ContDiff ℝ ∞ f) (x : Vec) :
    laplacian (fun y => c • f y) x = c • laplacian f x := by
  unfold laplacian
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (partialD i fun z => c • f z) = fun y => c • partialD i f y := by
    funext y; exact partialD_const_smul i c (hf.differentiable (by simp)) y
  rw [h1]
  exact partialD_const_smul i c ((contDiff_partialD i hf).differentiable (by simp)) x

