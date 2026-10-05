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

lemma sum_fiberwise (G : ℝ → ℝ) (k N : ℕ) (hk : 0 < k) :
    ∑ n ∈ Finset.range N, G (Int.fract (x n)) =
      ∑ i ∈ Finset.range k, ∑ n ∈ ((Finset.range N).filter fun n =>
        Int.fract (x n) ∈ Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)),
          G (Int.fract (x n)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hmaps : ∀ n ∈ Finset.range N, ⌊Int.fract (x n) * k⌋₊ ∈ Finset.range k := by
    intro n _
    have h1 : Int.fract (x n) * k < k := by
      nlinarith [Int.fract_lt_one (x n), Int.fract_nonneg (x n)]
    simp only [Finset.mem_range]
    exact (Nat.floor_lt (mul_nonneg (Int.fract_nonneg _) hkpos.le)).2 (by exact_mod_cast h1)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  exact Finset.sum_congr rfl fun i _ => by rw [filter_fiber_eq x k N hk i]

