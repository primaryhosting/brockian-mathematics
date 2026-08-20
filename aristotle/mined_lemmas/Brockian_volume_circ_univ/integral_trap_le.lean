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

lemma integral_trap_le {u v ε p : ℝ} (hε : 0 < ε) (hpu : p ≤ u) (huv : u ≤ v) (hv : v ≤ p + 1) :
    (∫ t in p..(p+1), trap u v ε t) ≤ v - u := by
  have hint : ∀ c d : ℝ, IntervalIntegrable (trap u v ε) volume c d :=
    fun c d => (continuous_trap u v ε).intervalIntegrable c d
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint p u) (hint u (p+1)),
    ← intervalIntegral.integral_add_adjacent_intervals (hint u v) (hint v (p+1))]
  have h1 : (∫ t in p..u, trap u v ε t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le hpu] at ht
      exact trap_eq_zero_of_le hε ht.2
  have h3 : (∫ t in v..(p+1), trap u v ε t) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_]
    · simp
    · intro t ht
      rw [Set.uIcc_of_le hv] at ht
      exact trap_eq_zero_of_ge hε ht.1
  have h2 : (∫ t in u..v, trap u v ε t) ≤ v - u := by
    calc (∫ t in u..v, trap u v ε t) ≤ ∫ _t in u..v, (1:ℝ) :=
          intervalIntegral.integral_mono_on huv (hint u v) intervalIntegrable_const
            (fun t _ => trap_le_one _ _ _ _)
      _ = v - u := by simp
  rw [h1, h3]
  linarith

