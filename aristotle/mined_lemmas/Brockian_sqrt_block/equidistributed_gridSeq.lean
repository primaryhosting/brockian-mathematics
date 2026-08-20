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

theorem equidistributed_gridSeq : Equidistributed gridSeq := by
  intro a b ha hab hb
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (6 / ε)
  refine ⟨(K₀ + 1) ^ 2, fun N hN => ?_⟩
  set K := Nat.sqrt N
  have hK1 : K₀ + 1 ≤ K := Nat.le_sqrt'.mpr hN
  have hKpos : 0 < K := by omega
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hKpos
  have hK0R : 6 / ε < (K : ℝ) := by
    refine lt_of_lt_of_le hK₀ ?_
    exact_mod_cast (by omega : K₀ ≤ K)
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hKN' : ((K : ℝ)) ^ 2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
  have hbound := abs_windowCount_sub_le ha hab hb N
  rw [Real.dist_eq]
  have heq : (windowCount gridSeq a b N : ℝ) / N - (b - a)
      = ((windowCount gridSeq a b N : ℝ) - N * (b - a)) / N := by field_simp
  rw [heq, abs_div, abs_of_pos hNR, div_lt_iff₀ hNR]
  have h6 : 6 < ε * K := by
    rw [div_lt_iff₀ hε] at hK0R; linarith
  have hεK : 6 * (K : ℝ) < ε * (K : ℝ) ^ 2 := by nlinarith
  have hεN : ε * (K : ℝ) ^ 2 ≤ ε * N := by nlinarith
  linarith

/-- Equidistributed sequences exist, so the hypothesis of `configCount_density_of_BV`
is satisfiable. -/
