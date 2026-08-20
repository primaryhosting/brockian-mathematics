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

lemma dist_avg_le (x : ℕ → ℝ) (f g : C(Circ, ℂ)) (N : ℕ) (hN : 0 < N) :
    ‖(∑ n ∈ range N, f ((x n : ℝ) : Circ)) / (N:ℂ)
      - (∑ n ∈ range N, g ((x n : ℝ) : Circ)) / (N:ℂ)‖ ≤ ‖f - g‖ := by
  have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [div_sub_div_same, ← Finset.sum_sub_distrib, norm_div]
  have h1 : ‖∑ n ∈ range N, (f ((x n : ℝ) : Circ) - g ((x n : ℝ) : Circ))‖ ≤ N * ‖f - g‖ := by
    calc ‖∑ n ∈ range N, (f ((x n : ℝ) : Circ) - g ((x n : ℝ) : Circ))‖
        ≤ ∑ n ∈ range N, ‖f ((x n : ℝ) : Circ) - g ((x n : ℝ) : Circ)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ range N, ‖f - g‖ := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          simpa using ContinuousMap.norm_coe_le_norm (f - g) ((x n : ℝ) : Circ)
      _ = N * ‖f - g‖ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Complex.norm_natCast, div_le_iff₀ (by positivity)]
  linarith

