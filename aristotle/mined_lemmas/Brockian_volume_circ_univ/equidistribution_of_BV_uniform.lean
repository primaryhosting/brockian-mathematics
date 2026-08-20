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

theorem equidistribution_of_BV_uniform {x : ℕ → ℝ} (hW : WeylCondition x) :
    EquidistributedMod1 x := by
  intro a b ha hab hb
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp only [Set.Ico_self, Set.mem_empty_iff_false, Finset.filter_false, Finset.card_empty,
      Nat.cast_zero, zero_div, sub_self]
    exact tendsto_const_nhds
  · rcases lt_or_eq_of_le (show b - a ≤ 1 by linarith) with hltb | heq
    · exact tendsto_count_of_weyl hW ha hlt hb hltb
    · have ha0 : a = 0 := by linarith
      have hb1 : b = 1 := by linarith
      subst ha0; subst hb1
      rw [show (1:ℝ) - 0 = 1 by ring]
      apply Tendsto.congr' _ (tendsto_const_nhds (x := (1:ℝ)))
      filter_upwards [eventually_gt_atTop 0] with N hN
      rw [Finset.filter_true_of_mem (fun n _ => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩),
        Finset.card_range, div_self (by exact_mod_cast hN.ne' : (N:ℝ) ≠ 0)]

/-- For irrational `α` the sequence `n ↦ n α` satisfies Weyl's exponential-sum condition:
the sums are geometric series with ratio `≠ 1`, hence bounded. -/
