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

theorem differentiable_time {u : ℝ → Vec → Vec}
    (h : ContDiff ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)) (x : Vec) :
    Differentiable ℝ (fun s => u s x) :=
  (h.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)

/-! ## The trivial (zero) solution: the base case -/

