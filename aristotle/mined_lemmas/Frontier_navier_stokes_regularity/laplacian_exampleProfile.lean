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

theorem laplacian_exampleProfile (nu t : ℝ) (x : Vec) :
    laplacian (exampleProfile nu t) x = -exampleProfile nu t x := by
  have key : partialD (partialD (exampleProfile nu t) 1) 1 x = -exampleProfile nu t x := by
    rw [partialD_exampleProfile_one,
      partialD_comp_coord (g' := fun u => -Real.sin u) (fun u => Real.hasDerivAt_cos u)]
    simp [exampleProfile]
  have h0 : partialD (partialD (exampleProfile nu t) 0) 0 x = 0 := by
    rw [partialD_exampleProfile_ne nu t (by decide : (0 : Fin 3) ≠ 1)]; simp
  have h2 : partialD (partialD (exampleProfile nu t) 2) 2 x = 0 := by
    rw [partialD_exampleProfile_ne nu t (by decide : (2 : Fin 3) ≠ 1)]; simp
  rw [laplacian, Fin.sum_univ_three, h0, h2, key]
  ring

