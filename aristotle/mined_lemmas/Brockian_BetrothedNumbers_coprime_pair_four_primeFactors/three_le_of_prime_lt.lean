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

lemma three_le_of_prime_lt {p q : ℕ} (hq : q.Prime) (hp : 2 ≤ p) (h : p < q) : 3 ≤ q := by
  have := hq.two_le; omega

/-- A prime larger than `3` is at least `5`. -/
