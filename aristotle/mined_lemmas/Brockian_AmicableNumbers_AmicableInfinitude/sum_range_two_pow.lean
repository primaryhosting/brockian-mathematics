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

/-
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Whether there are infinitely many amicable numbers is an open problem.  What is proved here
is an unconditional formalisation of Thabit ibn Qurra's rule together with the resulting
*conditional reduction*: if there are infinitely many Thabit indices `k` (i.e. indices for
which `3·2^(k-1) - 1`, `3·2^k - 1` and `9·2^(2k-1) - 1` are all prime), then there are
infinitely many amicable numbers.
-/

namespace Brockian.AmicableNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The sum of the proper divisors of `n` (the classical `s`-function). -/

lemma sum_range_two_pow (n : ℕ) : ∑ j ∈ range (n + 1), 2 ^ j = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have : (1 : ℕ) ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
      have : (2 : ℕ) ^ (k + 1 + 1) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
      omega

