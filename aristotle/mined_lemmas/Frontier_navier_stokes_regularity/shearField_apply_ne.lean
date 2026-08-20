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

theorem shearField_apply_ne (w : ℝ → Vec → ℝ) (t : ℝ) (x : Vec) {j : Fin 3} (hj : j ≠ 0) :
    shearField w t x j = 0 := by
  simp [shearField, hj]

