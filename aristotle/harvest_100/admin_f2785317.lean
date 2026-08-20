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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Obstruction

/-- The exponential coefficient `4π(A-1)` is positive when the bandwidth `A` exceeds `1`. -/
theorem coeff_pos {A : ℝ} (hA : 1 < A) : 0 < 4 * Real.pi * (A - 1) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have : 0 < A - 1 := by linarith
  positivity

/--
**Damage Cost Exponent Law.**
For any bandwidth `A > 1`, the rescaled deep-pair damage/cost ratio
`y ↦ exp (4π(A-1)y)` is strictly increasing and unbounded above:
for every `C > 0` there is some `y > 0` with `exp (4π(A-1)y) > C`.
-/
theorem damage_cost_exponent_law {A : ℝ} (hA : 1 < A) :
    StrictMono (fun y : ℝ => Real.exp (4 * Real.pi * (A - 1) * y)) ∧
      ∀ C : ℝ, 0 < C → ∃ y : ℝ, 0 < y ∧ C < Real.exp (4 * Real.pi * (A - 1) * y) := by
  have hk : 0 < 4 * Real.pi * (A - 1) := coeff_pos hA
  refine ⟨Real.exp_strictMono.comp (strictMono_mul_left_of_pos hk), ?_⟩
  intro C hC
  refine ⟨(|Real.log C| + 1) / (4 * Real.pi * (A - 1)), by positivity, ?_⟩
  have hy : 4 * Real.pi * (A - 1) * ((|Real.log C| + 1) / (4 * Real.pi * (A - 1)))
      = |Real.log C| + 1 := by
    rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hk)]
  rw [hy]
  calc C = Real.exp (Real.log C) := (Real.exp_log hC).symm
    _ < Real.exp (|Real.log C| + 1) := by
        apply Real.exp_lt_exp.mpr
        have := le_abs_self (Real.log C)
        linarith

end Zeta23Obstruction

