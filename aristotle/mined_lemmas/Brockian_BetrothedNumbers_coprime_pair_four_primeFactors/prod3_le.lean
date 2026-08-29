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

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction

/-- A *betrothed* (quasi-amicable) pair: two distinct positive integers `m ≠ n` such that
the sum of the divisors of each equals `m + n + 1`, i.e. each is the sum of the *nontrivial*
divisors (excluding `1` and the number itself) of the other. -/

private lemma prod3_le {x y z X Y Z : ℚ} (hx1 : 1 ≤ x) (hy1 : 1 ≤ y) (hz1 : 1 ≤ z)
    (hx : x ≤ X) (hy : y ≤ Y) (hz : z ≤ Z) : x * y * z ≤ X * Y * Z := by
  have h1 : x * y ≤ X * Y := mul_le_mul hx hy (by linarith) (by linarith)
  exact mul_le_mul h1 hz (by linarith) (by nlinarith)

/-- For three distinct primes, `∏ p/(p-1) ≤ 2 · (3/2) · (5/4) = 15/4`. -/
