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

import Brockian.EquidistributionBVReduction

/-!
# Existence of an equidistributed sequence

This file exhibits an explicit sequence which is equidistributed mod one in the sense of
`Brockian.EquidistributionBVReduction.Equidistributed`, so that the hypotheses of
`Brockian.EquidistributionBVReduction.configCount_density_of_BV` are satisfiable.

The sequence is the concatenation of the uniform grids of odd sizes: the `k`-th block consists
of the `2k+1` points `0/(2k+1), 1/(2k+1), …, 2k/(2k+1)`, and it occupies the indices
`k² ≤ n < (k+1)²`.  Since `Nat.sqrt n = k` exactly on that range of indices, the sequence has the
closed form `gridSeq n = (n - (sqrt n)²) / (2 * sqrt n + 1)`.
-/

open scoped BigOperators
open scoped Classical
open Filter Set

namespace Brockian
namespace EquidistributionBVReduction

/-- The concatenation of the uniform grids of odd sizes: the block of indices
`k² ≤ n < (k+1)²` runs through the `2k+1` points `j / (2k+1)`. -/

lemma windowCount_gridSeq_sq (a b : ℝ) (K : ℕ) :
    windowCount gridSeq a b (K ^ 2) = ∑ k ∈ Finset.range K, blockCount a b (2 * k + 1) := by
  have hcard : ∀ (N : ℕ), windowCount gridSeq a b N
      = ∑ n ∈ Finset.range N, if Int.fract (gridSeq n) ∈ Set.Ico a b then 1 else 0 := by
    intro N; rw [windowCount, Finset.card_filter]
  induction K with
  | zero => simp [windowCount, blockCount]
  | succ K ih =>
    have hle : K ^ 2 ≤ (K + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ K) 2
    have hlen : (K + 1) ^ 2 - K ^ 2 = 2 * K + 1 := by ring_nf; omega
    have hsplit : ∑ n ∈ Finset.range ((K + 1) ^ 2),
          (if Int.fract (gridSeq n) ∈ Set.Ico a b then 1 else 0)
        = (∑ n ∈ Finset.range (K ^ 2), if Int.fract (gridSeq n) ∈ Set.Ico a b then 1 else 0)
          + ∑ n ∈ Finset.Ico (K ^ 2) ((K + 1) ^ 2),
              if Int.fract (gridSeq n) ∈ Set.Ico a b then 1 else 0 := by
      rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (Nat.zero_le _) hle]
    rw [Finset.sum_range_succ, ← ih, hcard, hcard, hsplit]
    congr 1
    rw [blockCount, Finset.card_filter, Finset.sum_Ico_eq_sum_range, hlen]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < 2 * K + 1 := Finset.mem_range.mp hj
    rw [fract_gridSeq, gridSeq_block K j hj']
    push_cast
    ring_nf

/-- Over the first `K²` terms the window count is `K² (b-a)` up to an error `K`. -/
