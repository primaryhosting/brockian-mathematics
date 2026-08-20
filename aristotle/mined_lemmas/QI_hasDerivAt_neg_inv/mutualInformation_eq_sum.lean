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

import Mathlib

/-!
# Scalar integrals used in the integral representations
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace QI


theorem mutualInformation_eq_sum (hp0 : ∀ x, 0 ≤ p x) (hρpd : ∀ x, (ρ x).PosDef)
    (hρ : ∀ x, (ρ x).trace = 1) (hE : IsPOVM E) :
    mutualInformation (measureDist p ρ E)
      = ∑ x, p x * ∑ y, ((ρ x * E y).trace.re * Real.log ((ρ x * E y).trace.re)
          - (ρ x * E y).trace.re * Real.log ((ensembleAvg p ρ * E y).trace.re)) := by
  classical
  have hq0 : ∀ x y, 0 ≤ (ρ x * E y).trace.re := fun x y =>
    trace_mul_nonneg (hρpd x) (hE.posSemidef y)
  have hrow : ∀ x, ∑ y, measureDist p ρ E x y = p x := by
    intro x
    simp only [measureDist]
    rw [← Finset.mul_sum]
    have : ∑ y, (ρ x * E y).trace.re = 1 := by
      rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.mul_sum, hE.sum_eq_one, mul_one, hρ x]
      simp
    rw [this, mul_one]
  have hcol : ∀ y, ∑ x, measureDist p ρ E x y = (ensembleAvg p ρ * E y).trace.re := by
    intro y
    simp only [measureDist, ensembleAvg]
    rw [trace_sum_smul_mul]
  simp only [mutualInformation, hrow, hcol]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  set q : ℝ := (ρ x * E y).trace.re with hqdef
  set r : ℝ := (ensembleAvg p ρ * E y).trace.re with hrdef
  have hmd : measureDist p ρ E x y = p x * q := rfl
  rw [hmd]
  rcases eq_or_lt_of_le (hp0 x) with hpx | hpx
  · simp [← hpx]
  · rw [mul_div_mul_left _ _ (ne_of_gt hpx)]
    have hlog : q * Real.log (q / r) = q * Real.log q - q * Real.log r := by
      rcases eq_or_lt_of_le (show (0:ℝ) ≤ q from hq0 x y) with hq | hq
      · simp [← hq]
      · have hr : 0 < r := by
          rw [hrdef, ← hcol y]
          refine lt_of_lt_of_le ?_ (Finset.single_le_sum
            (f := fun x' => measureDist p ρ E x' y)
            (fun x' _ => mul_nonneg (hp0 x') (hq0 x' y)) (Finset.mem_univ x))
          exact mul_pos hpx hq
        rw [Real.log_div (ne_of_gt hq) (ne_of_gt hr)]
        ring
    rw [mul_assoc, hlog]

/-- **The Holevo bound.**  For any ensemble `(pₓ, ρₓ)` of faithful quantum states and any POVM
measurement `E`, the mutual information between the label `x` and the measurement outcome is at
most the Holevo quantity `χ = S(∑ pₓ ρₓ) - ∑ pₓ S(ρₓ)` of the ensemble. -/
