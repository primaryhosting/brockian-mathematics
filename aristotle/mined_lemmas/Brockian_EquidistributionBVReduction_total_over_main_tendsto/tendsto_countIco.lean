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

lemma tendsto_countIco (heq : Equidistributed x) (ha : a ∈ Set.Icc (0:ℝ) 1)
    (hb : b ∈ Set.Icc (0:ℝ) 1) (hab : a ≤ b) :
    Tendsto (fun N : ℕ => (countIco x N a b : ℝ) / N) atTop (𝓝 (b - a)) := by
  have key : ∀ N : ℕ, (countIco x N a b : ℝ) / N
      = (countLt x N b : ℝ) / N - (countLt x N a : ℝ) / N := by
    intro N
    have h := countLt_add_countIco (x := x) (N := N) hab
    have h' : (countLt x N a : ℝ) + (countIco x N a b : ℝ) = (countLt x N b : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) h
    rw [div_sub_div_same]
    congr 1
    linarith
  simp only [key]
  exact (heq b hb).sub (heq a ha)

end Counting

section Monotone

variable {f : ℝ → ℝ} {x : ℕ → ℝ}

/-- Splitting the first `N` terms according to the cell `[k/m, (k+1)/m)` they belong to. -/
