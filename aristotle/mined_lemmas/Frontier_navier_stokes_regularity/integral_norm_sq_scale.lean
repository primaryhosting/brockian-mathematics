import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## Differential operators on `ℝ³` -/

/-- Three dimensional Euclidean space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The `i`-th partial derivative of a (vector or scalar valued) field on `ℝ³`. -/

lemma integral_norm_sq_scale (g : E3 → E3) {c : ℝ} (hc : 0 < c) :
    ∫ x : E3, ‖c • g (c • x)‖ ^ 2 = c ^ 2 * ((c ^ 3)⁻¹ * ∫ y : E3, ‖g y‖ ^ 2) := by
  have h1 : ∀ x : E3, ‖c • g (c • x)‖ ^ 2 = c ^ 2 * ‖g (c • x)‖ ^ 2 := by
    intro x
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [h1]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  rw [MeasureTheory.Measure.integral_comp_smul
    (μ := (MeasureTheory.volume : MeasureTheory.Measure E3)) (fun y : E3 => ‖g y‖ ^ 2) c]
  simp [abs_of_pos, inv_pos.mpr (pow_pos hc 3)]

/-- Scaling reduction for the Millennium Problem: the class of solvable initial data is
invariant under the Navier–Stokes scaling `u₀ ↦ c u₀(c ·)`. -/
