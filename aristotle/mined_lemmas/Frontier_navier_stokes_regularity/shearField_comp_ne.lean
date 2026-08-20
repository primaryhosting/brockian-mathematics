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

theorem shearField_comp_ne (w : ℝ → Vec → ℝ) (t : ℝ) {j : Fin 3} (hj : j ≠ 0) :
    (fun y => shearField w t y j) = fun _ => (0 : ℝ) := by
  funext y; simp [shearField, hj]

