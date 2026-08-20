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

lemma sum_circTrap_le_count {x : ℕ → ℝ} {a b ε p : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (hb : b ≤ 1)
    (N : ℕ) :
    (∑ n ∈ Finset.range N, circTrap p a b ε ((x n : ℝ) : Circ))
      ≤ (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) := by
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_le_sum (fun n _ => ?_)
  by_cases h : Int.fract (x n) ∈ Set.Ico a b
  · rw [if_pos h]
    exact circTrap_le_one _ _ _ _ _
  · rw [if_neg h]
    have hfr0 : 0 ≤ Int.fract (x n) := Int.fract_nonneg _
    have hfr1 : Int.fract (x n) < 1 := Int.fract_lt_one _
    rw [← coe_fract (x n)]
    obtain ⟨m, _, heq⟩ := circTrap_coe_rep p a b ε (Int.fract (x n))
    rw [heq]
    refine le_of_eq ?_
    by_contra hne
    have h1 : ¬ (Int.fract (x n) + m ≤ a) := fun hle => hne (trap_eq_zero_of_le hε hle)
    have h2 : ¬ (b ≤ Int.fract (x n) + m) := fun hge => hne (trap_eq_zero_of_ge hε hge)
    push_neg at h1 h2
    have hm0 : m = 0 := by
      have hm1 : (-1 : ℝ) < (m : ℝ) := by linarith
      have hm2 : (m : ℝ) < 1 := by linarith
      have hm1' : (-1 : ℤ) < m := by exact_mod_cast hm1
      have hm2' : m < (1 : ℤ) := by exact_mod_cast hm2
      omega
    subst hm0
    simp only [Int.cast_zero, add_zero] at h1 h2
    exact h ⟨h1.le, h2⟩

/-! ### Step 4: the main theorem -/

/-- Key sandwich estimate for a nondegenerate proper subinterval. -/
