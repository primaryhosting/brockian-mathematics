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

/-- The exponential coefficient `4π(A−1)` is strictly positive when the bandwidth `A`
exceeds `1`. -/
theorem coeff_pos {A : ℝ} (hA : 1 < A) : 0 < 4 * Real.pi * (A - 1) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have : 0 < A - 1 := by linarith
  positivity

/-- **Damage Cost Exponent Law.**  For any bandwidth `A > 1`, the rescaled deep-pair
damage/cost ratio `y ↦ exp (4π(A−1)y)` is strictly increasing and unbounded above. -/
theorem damage_cost_exponent_law {A : ℝ} (hA : 1 < A) :
    StrictMono (fun y : ℝ => Real.exp (4 * Real.pi * (A - 1) * y)) ∧
      ∀ C : ℝ, 0 < C → ∃ y : ℝ, 0 < y ∧ C < Real.exp (4 * Real.pi * (A - 1) * y) := by
  set k : ℝ := 4 * Real.pi * (A - 1) with hk
  have hkpos : 0 < k := coeff_pos hA
  constructor
  · intro a b hab
    exact Real.exp_lt_exp.mpr (by nlinarith)
  · intro C hC
    refine ⟨max 1 ((Real.log C + 1) / k), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
    · have hy : (Real.log C + 1) / k ≤ max 1 ((Real.log C + 1) / k) := le_max_right _ _
      have h1 : Real.log C + 1 ≤ k * max 1 ((Real.log C + 1) / k) :=
        (div_le_iff₀' hkpos).mp hy
      have h2 : C * Real.exp 1 ≤ Real.exp (k * max 1 ((Real.log C + 1) / k)) := by
        have := Real.exp_le_exp.mpr h1
        rwa [Real.exp_add, Real.exp_log hC] at this
      have h3 : C < C * Real.exp 1 := by
        nlinarith [Real.add_one_lt_exp (one_ne_zero : (1:ℝ) ≠ 0)]
      linarith

end Zeta23Obstruction

