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

/-- The rescaled deep-pair damage/cost ratio `y ↦ exp (4π(A-1)y)` is, for any bandwidth
`A > 1`, strictly increasing and unbounded above. -/
theorem damage_cost_exponent_law :
    ∀ A : ℝ, 1 < A →
      StrictMono (fun y : ℝ => Real.exp (4 * Real.pi * (A - 1) * y)) ∧
      ∀ C : ℝ, 0 < C → ∃ y : ℝ, 0 < y ∧ Real.exp (4 * Real.pi * (A - 1) * y) > C := by
  intro A hA
  have hk : 0 < 4 * Real.pi * (A - 1) := by
    have := Real.pi_pos
    nlinarith
  constructor
  · intro a b hab
    exact Real.exp_lt_exp.mpr (by nlinarith)
  · intro C hC
    refine ⟨(|Real.log C| + 1) / (4 * Real.pi * (A - 1)), by positivity, ?_⟩
    have hy : 4 * Real.pi * (A - 1) * ((|Real.log C| + 1) / (4 * Real.pi * (A - 1)))
        = |Real.log C| + 1 := by
      have hA1 : A - 1 ≠ 0 := by linarith
      field_simp
    rw [hy]
    calc C = Real.exp (Real.log C) := (Real.exp_log hC).symm
      _ < Real.exp (|Real.log C| + 1) := by
          have := le_abs_self (Real.log C)
          exact Real.exp_lt_exp.mpr (by linarith)

end Zeta23Obstruction

