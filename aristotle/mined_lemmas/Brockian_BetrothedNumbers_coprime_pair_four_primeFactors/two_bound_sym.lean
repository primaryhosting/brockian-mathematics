import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace Brockian

namespace BetrothedNumbers

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair:
both are positive and `σ m = σ n = m + n + 1`. -/

lemma two_bound_sym {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b) :
    a * b ≤ 4 * ((a - 1) * (b - 1)) := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact two_bound ha.two_le (three_le_of_prime_lt hb ha.two_le h)
  · calc a * b = b * a := by ring
      _ ≤ 4 * ((b - 1) * (a - 1)) := two_bound hb.two_le (three_le_of_prime_lt ha hb.two_le h)
      _ = 4 * ((a - 1) * (b - 1)) := by ring

/-- Symmetric three-prime version of `three_bound`. -/
