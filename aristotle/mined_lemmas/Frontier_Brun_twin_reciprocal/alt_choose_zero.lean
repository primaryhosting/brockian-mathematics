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
# Bonferroni / truncated inclusion-exclusion

The combinatorial heart of Brun's pure sieve: truncating the alternating sum over subsets
at an even level gives an upper bound for the indicator of the empty set.
-/

namespace Brun

open Finset

/-- Partial alternating sums of binomial coefficients. -/

lemma alt_choose_zero (k : ℕ) :
    ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * (((0:ℕ)).choose j) = 1 := by
  have : ∀ j ∈ range (k + 1), (-1 : ℝ) ^ j * (((0:ℕ)).choose j) = if j = 0 then 1 else 0 := by
    intro j _
    rcases Nat.eq_zero_or_pos j with h | h
    · simp [h]
    · rw [Nat.choose_eq_zero_of_lt h]
      simp [Nat.ne_of_gt h]
  rw [Finset.sum_congr rfl this]
  simp

