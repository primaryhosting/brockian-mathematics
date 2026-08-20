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

lemma sum_lower_le_configCount (hg : MonotoneOn g (Set.Icc 0 1)) {m : ℕ} (hm : 0 < m) (N : ℕ) :
    ∑ i ∈ Finset.range m, g ((i : ℝ) / m) * (windowCount x ((i : ℝ) / m) (((i : ℝ) + 1) / m) N : ℝ)
      ≤ configCount g x N := by
  have hmaps : ∀ n ∈ Finset.range N, cellIdx x m n ∈ Finset.range m :=
    fun n _ => Finset.mem_range.mpr (cellIdx_lt hm n)
  rw [configCount, ← Finset.sum_fiberwise_of_maps_to hmaps (fun n => g (Int.fract (x n)))]
  apply Finset.sum_le_sum
  intro i hi
  rw [← filter_cellIdx_eq (x := x) hm N i]
  have hle : ∑ _n ∈ (Finset.range N).filter (fun n => cellIdx x m n = i), g ((i : ℝ) / m)
      ≤ ∑ n ∈ (Finset.range N).filter (fun n => cellIdx x m n = i), g (Int.fract (x n)) := by
    apply Finset.sum_le_sum
    intro n hn
    have hmem := (cellIdx_eq_iff hm n i).mp (Finset.mem_filter.mp hn).2
    exact hg (node_mem hm hi).1 ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩ hmem.1
  simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hle

/-- Upper step-function bound for the configuration count of a monotone weight. -/
