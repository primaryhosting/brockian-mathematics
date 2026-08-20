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

theorem partialD_exampleProfile_one (nu t : ℝ) :
    partialD (exampleProfile nu t) 1 = fun x : Vec => Real.exp (-nu * t) * Real.cos (x 1) := by
  funext x
  have he : exampleProfile nu t = fun y : Vec => Real.exp (-nu * t) * Real.sin (y 1) := rfl
  rw [he, partialD_comp_coord Real.hasDerivAt_sin]
  simp

