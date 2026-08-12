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

/-- The rescaled deep-pair damage/cost ratio `y ↦ exp (4π(A-1)y)` is strictly increasing
and unbounded above, for any bandwidth `A > 1`. -/
theorem damage_cost_exponent_law (A : ℝ) (hA : 1 < A) :
    StrictMono (fun y : ℝ => Real.exp (4 * Real.pi * (A - 1) * y)) ∧
      ∀ C : ℝ, 0 < C → ∃ y : ℝ, 0 < y ∧ C < Real.exp (4 * Real.pi * (A - 1) * y) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hk : 0 < 4 * Real.pi * (A - 1) := by nlinarith
  refine ⟨fun a b hab => Real.exp_lt_exp.mpr (by nlinarith), fun C hC => ?_⟩
  refine ⟨(|Real.log C| + 1) / (4 * Real.pi * (A - 1)), by positivity, ?_⟩
  have hy : 4 * Real.pi * (A - 1) * ((|Real.log C| + 1) / (4 * Real.pi * (A - 1)))
      = |Real.log C| + 1 := mul_div_cancel₀ _ (ne_of_gt hk)
  rw [hy]
  have h1 : Real.log C < |Real.log C| + 1 := by
    have := le_abs_self (Real.log C); linarith
  calc C = Real.exp (Real.log C) := (Real.exp_log hC).symm
    _ < Real.exp (|Real.log C| + 1) := Real.exp_lt_exp.mpr h1

end Zeta23Obstruction

