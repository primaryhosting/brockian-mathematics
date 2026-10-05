import Mathlib

/-!
# Damage Cost Exponent Law
Category: Brockian Corpus
Target: Zeta23Obstruction.damage_cost_exponent_law
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

namespace Zeta23Obstruction

/-- The exponential coefficient `4 * π * (A - 1)` is strictly positive when `A > 1`. -/

theorem damage_cost_exponent_law :
    ∀ A : ℝ, 1 < A →
      StrictMono (fun y : ℝ => Real.exp (4 * Real.pi * (A - 1) * y)) ∧
      ∀ C : ℝ, 0 < C → ∃ y : ℝ, 0 < y ∧ C < Real.exp (4 * Real.pi * (A - 1) * y) := by
  intro A hA
  have hk : 0 < 4 * Real.pi * (A - 1) := coeff_pos hA
  refine ⟨?_, ?_⟩
  · intro a b hab
    exact Real.exp_lt_exp.mpr (by nlinarith)
  · intro C hC
    refine ⟨(|Real.log C| + 1) / (4 * Real.pi * (A - 1)), by positivity, ?_⟩
    have hy : 4 * Real.pi * (A - 1) * ((|Real.log C| + 1) / (4 * Real.pi * (A - 1)))
        = |Real.log C| + 1 := by
      field_simp
      rw [div_self (sub_ne_zero_of_ne hA.ne')]
    rw [hy]
    calc C = Real.exp (Real.log C) := (Real.exp_log hC).symm
      _ < Real.exp (|Real.log C| + 1) := by
          have := le_abs_self (Real.log C)
          exact Real.exp_lt_exp.mpr (by linarith)

end Zeta23Obstruction

