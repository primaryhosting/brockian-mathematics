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

lemma abs_windowCount_sq_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (K : ℕ) :
    |(windowCount gridSeq a b (K ^ 2) : ℝ) - (K : ℝ) ^ 2 * (b - a)| ≤ K := by
  have hsum : ∀ J : ℕ, ∑ k ∈ Finset.range J, ((2 * k + 1 : ℕ) : ℝ) = (J : ℝ) ^ 2 := by
    intro J
    induction J with
    | zero => simp
    | succ J ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [windowCount_gridSeq_sq]
  push_cast
  have hrw : (∑ k ∈ Finset.range K, (blockCount a b (2 * k + 1) : ℝ)) - (K : ℝ) ^ 2 * (b - a)
      = ∑ k ∈ Finset.range K,
          ((blockCount a b (2 * k + 1) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) * (b - a)) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
  rw [hrw]
  calc |∑ k ∈ Finset.range K,
          ((blockCount a b (2 * k + 1) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) * (b - a))|
      ≤ ∑ k ∈ Finset.range K,
          |(blockCount a b (2 * k + 1) : ℝ) - ((2 * k + 1 : ℕ) : ℝ) * (b - a)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range K, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => abs_blockCount_sub_le ha hab hb (Nat.succ_pos _))
    _ = K := by simp

