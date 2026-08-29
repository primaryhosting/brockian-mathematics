import Mathlib

/-!
# Prime Power Member Structure
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.primePower_member_structure
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

open Finset
open scoped ArithmeticFunction.sigma

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive, they are distinct,
and the sum of the divisors of each, other than the number itself and `1`, gives the other;
equivalently `σ m = σ n = m + n + 1`. -/

lemma sigma_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    σ 1 (p ^ a) = ∑ i ∈ range (a + 1), p ^ i := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow hp]

