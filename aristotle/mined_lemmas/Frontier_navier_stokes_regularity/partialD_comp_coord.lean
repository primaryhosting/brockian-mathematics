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

theorem partialD_comp_coord {g g' : ℝ → ℝ} (hg : ∀ u : ℝ, HasDerivAt g (g' u) u)
    (c : ℝ) (i : Fin 3) (x : Vec) :
    partialD (fun y : Vec => c * g (y 1)) i x = c * g' (x 1) * (if i = 1 then 1 else 0) := by
  have h1 : HasFDerivAt (fun y : Vec => y 1) (ContinuousLinearMap.proj 1 : Vec →L[ℝ] ℝ) x :=
    (ContinuousLinearMap.proj 1 : Vec →L[ℝ] ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun y : Vec => g (y 1))
      (g' (x 1) • (ContinuousLinearMap.proj 1 : Vec →L[ℝ] ℝ)) x :=
    (hg (x 1)).comp_hasFDerivAt x h1
  have h3 : HasFDerivAt (fun y : Vec => c * g (y 1))
      ((c * g' (x 1)) • (ContinuousLinearMap.proj 1 : Vec →L[ℝ] ℝ)) x := by
    rw [← smul_smul]; exact h2.const_mul c
  rw [partialD, h3.fderiv]
  simp [Pi.single_apply, eq_comm]

/-- An explicit, nonzero shear profile: `w t x = exp (-nu t) * sin x₁`. -/
