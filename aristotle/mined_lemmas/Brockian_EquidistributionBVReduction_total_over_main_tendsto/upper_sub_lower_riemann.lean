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
# Reduction of equidistribution statements to functions of bounded variation

This file develops the classical "bounded variation reduction" step in equidistribution
theory: if a sequence `x : ℕ → ℝ` taking values in `[0, 1)` is equidistributed (i.e. the
proportion of the first `N` terms lying below `c` tends to `c` for every `c ∈ [0,1]`), then
for every function `f` of bounded variation on `[0,1]` the averages
`(1/N) * ∑_{n < N} f (x n)` converge to `∫₀¹ f`.

The final statement `total_over_main_tendsto` says that the *total* sum `∑_{n < N} f (x n)`
divided by the *main term* `N * ∫₀¹ f` tends to `1`, whenever the integral is nonzero.
-/

open Filter Finset MeasureTheory
open scoped Topology

namespace Brockian.EquidistributionBVReduction

/-- The number of indices `n < N` with `x n < c`. -/

lemma upper_sub_lower_riemann {m : ℕ} (hm : 0 < m) :
    (∑ k ∈ Finset.range m, f (((k : ℝ) + 1) / m) * (1 / m))
      - ∑ k ∈ Finset.range m, f (k / m) * (1 / m) = (f 1 - f 0) / m := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  rw [← Finset.sum_sub_distrib]
  have : ∀ k ∈ Finset.range m,
      f (((k : ℝ) + 1) / m) * (1 / m) - f (k / m) * (1 / m)
        = ((fun j : ℕ => f ((j : ℝ) / m) * (1 / m)) (k + 1))
          - ((fun j : ℕ => f ((j : ℝ) / m) * (1 / m)) k) := by
    intro k _
    simp only
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl this, Finset.sum_range_sub (fun j : ℕ => f ((j : ℝ) / m) * (1 / m))]
  simp only [Nat.cast_zero, zero_div]
  rw [div_self (ne_of_gt hm')]
  ring

/-- Averages of a monotone function along an equidistributed sequence converge to its
integral. -/
