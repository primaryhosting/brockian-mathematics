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

lemma sigma_one_two_pow_mul_odd_prime {k p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    σ₁ (2 ^ k * p) = (σ₁ (2 ^ k)) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p := (Nat.coprime_two_left.mpr hodd).pow_left k
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_prime hp]

/-- **Unique partner.** If `σ₁ (2 ^ k * p) = 2 ^ k * p + m + 1` for an odd prime `p`, then
`m = (2 ^ k - 1) * (p + 2)`. -/
