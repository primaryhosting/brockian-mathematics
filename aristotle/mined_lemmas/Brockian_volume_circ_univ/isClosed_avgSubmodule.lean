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
# Weyl's equidistribution criterion, via reduction of BV (indicator) test functions

This file proves the classical **Weyl criterion** (sufficiency direction):
if all nontrivial exponential sums along a real sequence `x : ℕ → ℝ` have vanishing
Cesàro averages, then `x` is equidistributed modulo one in the counting sense.

The proof proceeds by the *BV reduction*: the characteristic function of an interval
(a function of bounded variation) is squeezed between continuous trapezoidal functions
on the circle, and continuous functions on the circle are approximated uniformly by
trigonometric polynomials.

As an application, the sequence `n ↦ n * α` is equidistributed mod one for irrational `α`.
-/

open Filter Topology MeasureTheory Finset

namespace Brockian
namespace EquidistributionBVReduction

noncomputable section

open scoped Classical

instance factOnePos : Fact ((0:ℝ) < 1) := ⟨one_pos⟩

/-- The circle `ℝ / ℤ`. -/
abbrev Circ := AddCircle (1:ℝ)

/-- `x : ℕ → ℝ` is equidistributed modulo one: for every subinterval `[a, b) ⊆ [0,1]`,
the proportion of the first `N` terms whose fractional part lies in `[a, b)` tends to
`b - a`. -/

lemma isClosed_avgSubmodule (x : ℕ → ℝ) :
    IsClosed ((avgSubmodule x : Submodule ℂ C(Circ, ℂ)) : Set C(Circ, ℂ)) := by
  apply isClosed_of_closure_subset
  intro f hf
  rw [SetLike.mem_coe, mem_avgSubmodule, AvgTendsto, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgS, hgd⟩ := Metric.mem_closure_iff.1 hf (ε/3) (by linarith)
  have hg : AvgTendsto x g := (mem_avgSubmodule x g).1 hgS
  rw [AvgTendsto, Metric.tendsto_atTop] at hg
  obtain ⟨N₀, hN₀⟩ := hg (ε/3) (by linarith)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 0 < N := lt_of_lt_of_le Nat.zero_lt_one (le_trans (le_max_right N₀ 1) hN)
  have hfg : ‖f - g‖ < ε/3 := by rw [← dist_eq_norm]; exact hgd
  have h1 : dist ((∑ n ∈ range N, f ((x n:ℝ) : Circ)) / (N:ℂ))
      ((∑ n ∈ range N, g ((x n:ℝ) : Circ)) / (N:ℂ)) < ε/3 := by
    rw [dist_eq_norm]; exact lt_of_le_of_lt (dist_avg_le x f g N hN1) hfg
  have h3 := hN₀ N (le_trans (le_max_left N₀ 1) hN)
  have h2 : dist (∫ t : Circ, g t) (∫ t : Circ, f t) < ε/3 := by
    rw [dist_eq_norm, norm_sub_rev]
    exact lt_of_le_of_lt (norm_integral_sub_le f g) hfg
  calc dist ((∑ n ∈ range N, f ((x n:ℝ) : Circ)) / (N:ℂ)) (∫ t : Circ, f t)
      ≤ dist ((∑ n ∈ range N, f ((x n:ℝ) : Circ)) / (N:ℂ))
            ((∑ n ∈ range N, g ((x n:ℝ) : Circ)) / (N:ℂ))
        + dist ((∑ n ∈ range N, g ((x n:ℝ) : Circ)) / (N:ℂ)) (∫ t : Circ, g t)
        + dist (∫ t : Circ, g t) (∫ t : Circ, f t) := dist_triangle4 _ _ _ _
    _ < ε/3 + ε/3 + ε/3 := by linarith
    _ = ε := by ring

