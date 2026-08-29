/-
# Damage Cost Exponent Law
Category: Brockian Corpus
Target: Zeta23Obstruction.damage_cost_exponent_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

set_option grind.warning false

namespace Zeta23Obstruction

/-- The rescaled deep-pair damage/cost ratio `y ↦ exp (4π(A-1)y)` is strictly increasing
and unbounded, for any bandwidth `A > 1`. -/
theorem damage_cost_exponent_law (A : ℝ) (hA : 1 < A) :
    StrictMono (fun y : ℝ => Real.exp (4 * Real.pi * (A - 1) * y)) ∧
      ∀ C : ℝ, 0 < C → ∃ y : ℝ, 0 < y ∧ Real.exp (4 * Real.pi * (A - 1) * y) > C := by
  have hpos : 0 < 4 * Real.pi * (A - 1) := by
    have := Real.pi_pos
    nlinarith
  constructor
  · intro a b hab
    exact Real.exp_lt_exp.mpr (by nlinarith)
  · intro C hC
    set L : ℝ := max (Real.log C) 0 + 1 with hL
    have hL1 : 0 < L := by
      have : (0:ℝ) ≤ max (Real.log C) 0 := le_max_right _ _
      simp only [hL]; linarith
    have hLlog : Real.log C < L := by
      have : Real.log C ≤ max (Real.log C) 0 := le_max_left _ _
      simp only [hL]; linarith
    refine ⟨L / (4 * Real.pi * (A - 1)), div_pos hL1 hpos, ?_⟩
    have hmul : 4 * Real.pi * (A - 1) * (L / (4 * Real.pi * (A - 1))) = L := by
      field_simp
      exact div_self (sub_ne_zero.mpr hA.ne')
    rw [hmul]
    calc C = Real.exp (Real.log C) := (Real.exp_log hC).symm
      _ < Real.exp L := Real.exp_lt_exp.mpr hLlog

end Zeta23Obstruction

