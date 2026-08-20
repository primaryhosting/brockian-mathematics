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

lemma count_le_sum_circTrap {x : ℕ → ℝ} {a b ε p : ℝ} (hε : 0 < ε) (hpa : p ≤ a - ε)
    (hpb : b + ε ≤ p + 1) (N : ℕ) :
    (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ)
      ≤ ∑ n ∈ Finset.range N, circTrap p (a - ε) (b + ε) ε ((x n : ℝ) : Circ) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_le_sum (fun n _ => ?_)
  by_cases h : Int.fract (x n) ∈ Set.Ico a b
  · rw [if_pos h, ← coe_fract (x n),
      circTrap_coe (u := a - ε) (v := b + ε) ⟨by have := h.1; linarith, by have := h.2; linarith⟩,
      trap_eq_one hε (by have := h.1; linarith) (by have := h.2; linarith)]
  · rw [if_neg h]
    exact circTrap_nonneg _ _ _ _ _

/-- Counting is bounded below by the average of the inner trapezoid. -/
