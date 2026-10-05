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

lemma bonferroni {α : Type*} [DecidableEq α] (S : Finset α) (k : ℕ) (hk : Even k) :
    (if S = ∅ then (1 : ℝ) else 0) ≤ ∑ T ∈ S.powerset with #T ≤ k, (-1 : ℝ) ^ (#T) := by
  rw [sum_powerset_card_le]
  by_cases h : S = ∅
  · subst h
    simp only [Finset.card_empty]
    rw [alt_choose_zero]
    norm_num
  · rw [if_neg h]
    exact alt_choose_nonneg _ k hk

end Brun

