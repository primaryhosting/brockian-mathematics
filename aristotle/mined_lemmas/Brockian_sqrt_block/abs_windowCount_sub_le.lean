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

lemma abs_windowCount_sub_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (N : ℕ) :
    |(windowCount gridSeq a b N : ℝ) - N * (b - a)| ≤ 3 * Nat.sqrt N + 2 := by
  set K := Nat.sqrt N
  have hd0 : 0 ≤ b - a := by linarith
  have hd1 : b - a ≤ 1 := by linarith
  have hKN : K ^ 2 ≤ N := Nat.sqrt_le' N
  have hNK : N < (K + 1) ^ 2 := Nat.lt_succ_sqrt' N
  have hKN' : ((K : ℝ)) ^ 2 ≤ N := by exact_mod_cast hKN
  have hNK' : (N : ℝ) ≤ ((K : ℝ) + 1) ^ 2 := by
    have : (N : ℝ) < ((K + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hNK
    push_cast at this
    linarith
  have hlow : (windowCount gridSeq a b (K ^ 2) : ℝ) ≤ (windowCount gridSeq a b N : ℝ) := by
    exact_mod_cast windowCount_mono gridSeq a b hKN
  have hupp : (windowCount gridSeq a b N : ℝ) ≤ (windowCount gridSeq a b ((K + 1) ^ 2) : ℝ) := by
    exact_mod_cast windowCount_mono gridSeq a b hNK.le
  have h1 := abs_le.mp (abs_windowCount_sq_sub_le ha hab hb K)
  have h2 := abs_le.mp (abs_windowCount_sq_sub_le ha hab hb (K + 1))
  have hcast : (((K + 1 : ℕ)) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
  rw [hcast] at h2
  have hKnn : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  rw [abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- The explicit sequence `gridSeq` is equidistributed mod one. -/
