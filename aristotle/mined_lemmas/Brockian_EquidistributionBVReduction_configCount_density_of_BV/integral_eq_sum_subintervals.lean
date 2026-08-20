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
# An equidistributed sequence

This file exhibits a concrete sequence in `[0,1)` satisfying
`Brockian.EquidistributionBVReduction.Equidistributed`, showing that the equidistribution
hypothesis of `configCount_density_of_BV` is satisfiable (so the theorem is not vacuous).

The sequence is the "triangular block" sequence: the `k`-th block lists the `k+1` points
`0/(k+1), 1/(k+1), …, k/(k+1)`.
-/

open Filter Set
open scoped Topology

namespace Brockian.EquidistributionBVReduction

/-- Start index of block `k`; block `k` consists of the `k+1` indices
`blockStart k, …, blockStart k + k`. -/

lemma integral_eq_sum_subintervals (f : ℝ → ℝ) (hf : MonotoneOn f (Set.Icc 0 1)) {m : ℕ}
    (hm : 0 < m) :
    (∫ t in (0:ℝ)..1, f t)
      = ∑ i ∈ Finset.range m, ∫ t in ((i:ℝ)/m)..(((i:ℝ)+1)/m), f t := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hint : ∀ k < m,
      IntervalIntegrable f MeasureTheory.volume ((k:ℝ)/m) ((((k:ℕ)+1 : ℕ):ℝ)/m) := by
    intro k hk
    have hi1 : (k:ℝ) + 1 ≤ m := by exact_mod_cast hk
    have hab : (k:ℝ)/m ≤ ((k:ℝ)+1)/m := by gcongr; linarith
    have hsub : Set.Icc ((k:ℝ)/m) (((k:ℝ)+1)/m) ⊆ Set.Icc (0:ℝ) 1 := by
      intro t ht
      refine ⟨le_trans (by positivity) ht.1, le_trans ht.2 ?_⟩
      rw [div_le_one hm']; exact hi1
    have hmo : MonotoneOn f (Set.uIcc ((k:ℝ)/m) (((k:ℝ)+1)/m)) := by
      rw [Set.uIcc_of_le hab]; exact hf.mono hsub
    have h2 := hmo.intervalIntegrable (μ := MeasureTheory.volume)
    push_cast
    exact h2
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := MeasureTheory.volume)
    (f := f) (a := fun k : ℕ => (k:ℝ)/m) (n := m) hint
  simp only [Nat.cast_zero, zero_div, Nat.cast_add, Nat.cast_one, div_self (ne_of_gt hm')] at h
  exact h.symm

/-- The lower Riemann sum underestimates the integral. -/
