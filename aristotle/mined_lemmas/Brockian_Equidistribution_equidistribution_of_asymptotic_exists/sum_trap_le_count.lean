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

/-
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

open Filter Topology MeasureTheory Complex

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Brockian.Equidistribution

/-! ## Weyl averages of continuous functions on the circle -/

/-- The `N`-th Weyl average of a continuous function `f` on the circle `ℝ / ℤ`, sampled along the
orbit `n ↦ n • α` of the rotation by `α`. -/

theorem sum_trap_le_count (α a b δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    ∑ n ∈ Finset.range N, trap a b δ (Int.fract ((n : ℝ) * α)) ≤ (countIco α a b N : ℝ) := by
  classical
  have hcard : (countIco α a b N : ℝ)
      = ∑ n ∈ Finset.range N,
          if a ≤ Int.fract ((n : ℝ) * α) ∧ Int.fract ((n : ℝ) * α) < b then (1 : ℝ) else 0 := by
    unfold countIco
    rw [Finset.card_filter]
    push_cast
    rfl
  rw [hcard]
  refine Finset.sum_le_sum fun n _ => ?_
  by_cases h : a ≤ Int.fract ((n : ℝ) * α) ∧ Int.fract ((n : ℝ) * α) < b
  · simp [h, trap_le_one]
  · rw [if_neg h]
    push_neg at h
    rcases lt_or_ge (Int.fract ((n : ℝ) * α)) a with h1 | h1
    · rw [trap_eq_zero_of_le a b δ _ hδ h1.le]
    · rw [trap_eq_zero_of_ge a b δ _ hδ (h h1)]

