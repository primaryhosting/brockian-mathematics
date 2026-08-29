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
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.EquidistributionBVReduction

open Filter Set MeasureTheory

/-- `configCount x S N` is the number of indices `n < N` whose fractional part
`Int.fract (x n)` lands in the "configuration window" `S`. -/

lemma sum_integral_partition (G : ℝ → ℝ) (hG : Monotone G) (k : ℕ) (hk : 0 < k) :
    ∑ i ∈ Finset.range k, ∫ t in ((i : ℝ) / k)..(((i : ℝ) + 1) / k), G t =
      ∫ t in (0 : ℝ)..1, G t := by
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have h := intervalIntegral.sum_integral_adjacent_intervals
    (μ := MeasureTheory.volume) (a := fun i : ℕ => (i : ℝ) / k) (f := G) (n := k)
    (fun i _ => hG.intervalIntegrable)
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div] at h
  rw [div_self hkne] at h
  exact h

