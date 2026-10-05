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

lemma integral_le_upperSum (G : ℝ → ℝ) (hG : Monotone G) (k : ℕ) (hk : 0 < k) :
    (∫ t in (0 : ℝ)..1, G t) ≤ upperSum G k := by
  rw [← sum_integral_partition G hG k hk]
  refine Finset.sum_le_sum fun i _ => ?_
  have hle := div_le_div_succ i k hk
  have hmono := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hle
    hG.intervalIntegrable intervalIntegrable_const
    (fun t ht => hG ht.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hval : (((i : ℝ) + 1) / k - (i : ℝ) / k) * G (((i : ℝ) + 1) / k)
      = G (((i : ℝ) + 1) / k) / k := by
    have : ((i : ℝ) + 1) / k - (i : ℝ) / k = 1 / k := by ring
    rw [this]; ring
  rw [hval] at hmono
  exact hmono

