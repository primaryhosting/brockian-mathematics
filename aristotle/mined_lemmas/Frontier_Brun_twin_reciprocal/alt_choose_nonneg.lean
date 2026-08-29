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

lemma alt_choose_nonneg (r k : ℕ) (hk : Even k) :
    (0 : ℝ) ≤ ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * (r.choose j) := by
  cases r with
  | zero => rw [alt_choose_zero]; norm_num
  | succ r =>
    rw [alt_choose_partial r k, hk.neg_one_pow]
    positivity

