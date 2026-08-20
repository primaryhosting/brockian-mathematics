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

lemma tendsto_step_average (hx : Equidistributed x) (c : ℕ → ℝ) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
        (∑ i ∈ Finset.range m, c i * (windowCount x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ)) / N)
      atTop (nhds (∑ i ∈ Finset.range m, c i / m)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  simp_rw [Finset.sum_div, mul_div_assoc]
  apply tendsto_finset_sum
  intro i hi
  have hi' : (i : ℝ) + 1 ≤ m := by exact_mod_cast Finset.mem_range.mp hi
  have h := hx ((i : ℝ) / m) (((i : ℝ) + 1) / m) (by positivity)
    (by apply div_le_div_of_nonneg_right <;> linarith)
    (by rw [div_le_one hm']; linarith)
  have hval : ((i : ℝ) + 1) / m - (i : ℝ) / m = 1 / m := by field_simp; ring
  rw [hval] at h
  rw [show c i / m = c i * (1 / m) by ring]
  exact h.const_mul (c i)

/-- The BV reduction for a monotone weight: the configuration counts of an equidistributed
sequence weighted by a monotone function have density the integral of that function. -/
