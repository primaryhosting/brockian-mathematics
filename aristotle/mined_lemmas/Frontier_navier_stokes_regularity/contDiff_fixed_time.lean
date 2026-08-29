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

theorem contDiff_fixed_time {u : ℝ → Vec → E}
    (h : ContDiff ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)) (t : ℝ) : ContDiff ℝ ∞ (u t) :=
  h.comp (contDiff_const.prodMk contDiff_id)

