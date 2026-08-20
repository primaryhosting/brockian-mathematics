import Mathlib
/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ContDiff
open MeasureTheory

namespace Frontier

/-! ## Basic differential operators on `ℝ³` -/

/-- The physical space `ℝ³`, as functions `Fin 3 → ℝ`. -/
abbrev Vec := Fin 3 → ℝ

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/

theorem smooth_exampleProfile (nu : ℝ) : SmoothScalarField (exampleProfile nu) := by
  have h1 : ContDiff ℝ ∞ fun q : ℝ × Vec => Real.exp (-nu * q.1) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst)
  have h2 : ContDiff ℝ ∞ fun q : ℝ × Vec => Real.sin (q.2 1) :=
    Real.contDiff_sin.comp ((contDiff_apply ℝ ℝ (1 : Fin 3)).comp contDiff_snd)
  exact h1.mul h2

