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

theorem exampleProfile_indep (nu : ℝ) (t : ℝ) (x : Vec) :
    partialD (exampleProfile nu t) 0 x = 0 := by
  rw [partialD_exampleProfile_ne nu t (by decide : (0 : Fin 3) ≠ 1)]

