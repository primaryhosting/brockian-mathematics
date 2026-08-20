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

lemma not_equidistributed_const : ¬ Equidistributed (fun _ : ℕ => (0:ℝ)) := by
  intro h
  have h2 := h (1/2) (by constructor <;> norm_num)
  have heq1 : ∀ᶠ N : ℕ in atTop, (countLt (fun _ : ℕ => (0:ℝ)) N (1/2) : ℝ) / N = 1 := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hcount : countLt (fun _ : ℕ => (0:ℝ)) N (1/2) = N := by
      unfold countLt
      rw [Finset.filter_true_of_mem (fun n _ => by norm_num), Finset.card_range]
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [hcount, div_self hN']
  have hcontra := tendsto_nhds_unique (h2.congr' heq1) tendsto_const_nhds
  norm_num at hcontra

section Counting

variable {x : ℕ → ℝ} {N : ℕ} {a b : ℝ}

