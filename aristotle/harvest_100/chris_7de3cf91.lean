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

/-- The coefficient `4π(A-1)` is strictly positive when `A > 1`. -/
lemma coeff_pos {A : ℝ} (hA : 1 < A) : 0 < 4 * Real.pi * (A - 1) := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have h : (0:ℝ) < A - 1 := by linarith
  positivity

/--
**Damage cost exponent law.** For any bandwidth `A > 1`, the rescaled deep-pair
damage/cost ratio `y ↦ exp (4π(A-1)y)` is strictly increasing and unbounded above.
-/
theorem damage_cost_exponent_law {A : ℝ} (hA : 1 < A) :
    StrictMono (fun y : ℝ => Real.exp (4 * Real.pi * (A - 1) * y)) ∧
      ∀ C > 0, ∃ y > 0, Real.exp (4 * Real.pi * (A - 1) * y) > C := by
  have hc : 0 < 4 * Real.pi * (A - 1) := coeff_pos hA
  refine ⟨fun a b hab => Real.exp_lt_exp.mpr (by nlinarith), ?_⟩
  intro C hC
  refine ⟨(|Real.log C| + 1) / (4 * Real.pi * (A - 1)), ?_, ?_⟩
  · positivity
  · have hy : 4 * Real.pi * (A - 1) * ((|Real.log C| + 1) / (4 * Real.pi * (A - 1)))
        = |Real.log C| + 1 := by
      rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hc)]
    rw [hy]
    have hge : Real.log C + 1 ≤ |Real.log C| + 1 := by
      have := le_abs_self (Real.log C); linarith
    have h1 : C < Real.exp (Real.log C + 1) := by
      rw [Real.exp_add, Real.exp_log hC]
      nlinarith [Real.exp_one_gt_d9]
    exact lt_of_lt_of_le h1 (Real.exp_le_exp.mpr hge)

end Zeta23Obstruction

