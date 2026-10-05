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

lemma tendsto_configCount_div (hx : EquidistributedMod1 x) (k i : ℕ) (hk : 0 < k)
    (hik : i < k) :
    Tendsto (fun N : ℕ =>
      (configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) / N) atTop
      (nhds (1 / k)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h0 : (0 : ℝ) ≤ (i : ℝ) / k := by positivity
  have hsplit : ((i : ℝ) + 1) / k = (i : ℝ) / k + 1 / k := by ring
  have h1k : (0 : ℝ) < 1 / k := by positivity
  have hab : (i : ℝ) / k ≤ ((i : ℝ) + 1) / k := by rw [hsplit]; linarith
  have hb1 : ((i : ℝ) + 1) / k ≤ 1 := by
    rw [div_le_one hkpos]
    have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hik
    linarith
  have h := hx ((i : ℝ) / k) (((i : ℝ) + 1) / k) h0 hab hb1
  have heq : ((i : ℝ) + 1) / k - (i : ℝ) / k = 1 / k := by rw [hsplit]; ring
  rwa [heq] at h

