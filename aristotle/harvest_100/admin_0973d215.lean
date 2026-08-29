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

namespace Zeta23Obstruction

/-- The rescaled deep-pair damage/cost ratio `y ↦ exp (4π(A-1)y)` is, for any bandwidth
`A > 1`, strictly increasing and unbounded above. -/
theorem damage_cost_exponent_law (A : ℝ) (hA : 1 < A) :
    StrictMono (fun y : ℝ => Real.exp (4 * Real.pi * (A - 1) * y)) ∧
      ∀ C : ℝ, 0 < C → ∃ y : ℝ, 0 < y ∧ Real.exp (4 * Real.pi * (A - 1) * y) > C := by
  have hk : 0 < 4 * Real.pi * (A - 1) := by
    have : 0 < A - 1 := by linarith
    positivity
  constructor
  · intro a b hab
    exact Real.exp_lt_exp.mpr (by nlinarith)
  · intro C hC
    refine ⟨max 1 ((Real.log C + 1) / (4 * Real.pi * (A - 1))), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
    have h1 : (Real.log C + 1) / (4 * Real.pi * (A - 1))
        ≤ max 1 ((Real.log C + 1) / (4 * Real.pi * (A - 1))) := le_max_right _ _
    have h2 : Real.log C + 1
        ≤ 4 * Real.pi * (A - 1) * max 1 ((Real.log C + 1) / (4 * Real.pi * (A - 1))) := by
      have := (div_le_iff₀ hk).mp h1
      linarith [this]
    have h3 : Real.exp (Real.log C + 1)
        ≤ Real.exp (4 * Real.pi * (A - 1) * max 1 ((Real.log C + 1) / (4 * Real.pi * (A - 1)))) :=
      Real.exp_le_exp.mpr h2
    have h4 : C < Real.exp (Real.log C + 1) := by
      rw [Real.exp_add, Real.exp_log hC]
      nlinarith [Real.add_one_lt_exp (one_ne_zero), hC]
    exact lt_of_lt_of_le h4 h3

end Zeta23Obstruction

