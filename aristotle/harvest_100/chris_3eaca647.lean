/-
# Damage Cost Exponent Law
Category: Brockian Corpus
Target: Zeta23Obstruction.damage_cost_exponent_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Damage Cost Exponent Law
Category: Brockian Corpus
Target: Zeta23Obstruction.damage_cost_exponent_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Zeta23Obstruction

/-- The coefficient `4π(A−1)` is strictly positive when `A > 1`. -/
lemma coeff_pos {A : ℝ} (hA : 1 < A) : 0 < 4 * Real.pi * (A - 1) :=
  mul_pos (by positivity) (sub_pos.mpr hA)

/--
**Damage Cost Exponent Law.**  For any bandwidth `A > 1`, the rescaled deep-pair
damage/cost ratio `y ↦ exp (4π(A−1) y)` is
1. strictly monotone, and
2. unbounded above: every `C > 0` is exceeded at some `y > 0`.
-/
theorem damage_cost_exponent_law {A : ℝ} (hA : 1 < A) :
    StrictMono (fun y : ℝ => Real.exp (4 * Real.pi * (A - 1) * y)) ∧
    ∀ C > 0, ∃ y > 0, Real.exp (4 * Real.pi * (A - 1) * y) > C := by
  have hk : 0 < 4 * Real.pi * (A - 1) := coeff_pos hA
  refine ⟨Real.exp_strictMono.comp (strictMono_mul_left_of_pos hk), ?_⟩
  intro C hC
  refine ⟨(|Real.log C| + 1) / (4 * Real.pi * (A - 1)), by positivity, ?_⟩
  have hmul : 4 * Real.pi * (A - 1) * ((|Real.log C| + 1) / (4 * Real.pi * (A - 1)))
      = |Real.log C| + 1 := by
    have hA1 : A - 1 ≠ 0 := sub_ne_zero.mpr hA.ne'
    field_simp
  rw [hmul, gt_iff_lt]
  calc C = Real.exp (Real.log C) := (Real.exp_log hC).symm
    _ < Real.exp (|Real.log C| + 1) :=
        Real.exp_lt_exp.mpr (by have := le_abs_self (Real.log C); linarith)

end Zeta23Obstruction

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

