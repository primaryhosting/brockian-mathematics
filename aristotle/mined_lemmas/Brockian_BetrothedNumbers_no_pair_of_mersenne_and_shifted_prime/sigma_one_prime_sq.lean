import Mathlib

/-!
# No Pair Of Mersenne And Shifted Prime
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.no_pair_of_mersenne_and_shifted_prime
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

set_option grind.warning false

open ArithmeticFunction

namespace Brockian
namespace BetrothedNumbers

/-- Sum-of-divisors function `σ₁`. -/
local notation "σ₁" => ArithmeticFunction.sigma 1

/-- Two positive naturals `n ≠ m` form a *betrothed* (quasi-amicable) pair when the sum of the
divisors of each of them equals `n + m + 1`. -/

lemma sigma_one_prime_sq {p : ℕ} (hp : p.Prime) : σ₁ (p ^ 2) = 1 + p + p ^ 2 := by
  rw [sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  simp [Finset.sum_range_succ]

/-- `σ₁` of a power of two, stated without natural subtraction. -/
