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

lemma upperSum_sub_lowerSum (G : ℝ → ℝ) (k : ℕ) (hk : 0 < k) :
    upperSum G k - lowerSum G k = (G 1 - G 0) / k := by
  have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have h1 : upperSum G k = ∑ i ∈ Finset.range k, G (((i + 1 : ℕ) : ℝ) / k) / k := by
    simp only [upperSum]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring_nf
  have h2 : lowerSum G k = ∑ i ∈ Finset.range k, G (((i : ℕ) : ℝ) / k) / k := rfl
  rw [h1, h2, ← Finset.sum_sub_distrib]
  have h3 : ∑ i ∈ Finset.range k,
      (G (((i + 1 : ℕ) : ℝ) / k) / k - G (((i : ℕ) : ℝ) / k) / k)
      = (∑ i ∈ Finset.range k,
          (G (((i + 1 : ℕ) : ℝ) / k) - G (((i : ℕ) : ℝ) / k))) / k := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h3, Finset.sum_range_sub (fun j : ℕ => G ((j : ℝ) / k)), div_self hkne, Nat.cast_zero,
    zero_div]

/-- The Cesàro averages of a monotone function along an equidistributed sequence
converge to its integral over `[0,1]`. -/
