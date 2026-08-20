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

lemma integral_le_upper_sum (hg : MonotoneOn g (Set.Icc 0 1)) (hm : 0 < m) :
    (∫ t in (0:ℝ)..1, g t) ≤ ∑ i ∈ Finset.range m, g (((i : ℝ) + 1) / m) / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hint := partition_integrable hg hm
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (i : ℝ) / m) (f := g) (μ := volume) hint
  simp only [Nat.cast_zero, zero_div, div_self hm'.ne'] at hsum
  rw [← hsum]
  apply Finset.sum_le_sum
  intro i hi
  have him := Finset.mem_range.mp hi
  have hik : (i : ℝ) / m ≤ ((i + 1 : ℕ) : ℝ) / m := partition_mono hm (Nat.le_succ i)
  have key := intervalIntegral.integral_mono_on (μ := volume) hik (hint i him)
    (intervalIntegrable_const (c := g (((i + 1 : ℕ) : ℝ) / m)))
    (fun t ht => hg (partition_sub hm him ht) (partition_sub hm him ⟨hik, le_refl _⟩) ht.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at key
  have hlen : ((i + 1 : ℕ) : ℝ) / m - (i : ℝ) / m = 1 / m := by push_cast; field_simp; ring
  have hcast : ((i + 1 : ℕ) : ℝ) / m = ((i : ℝ) + 1) / m := by push_cast; ring
  rw [hlen, hcast,
    show (1 : ℝ) / m * g (((i : ℝ) + 1) / m) = g (((i : ℝ) + 1) / m) / m from by ring] at key
  rw [hcast]
  exact key

/-- The gap between the upper and the lower Riemann sum telescopes. -/
