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

namespace Brockian.BetrothedNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- The sum-of-divisors function `σ₁`. -/

lemma sigmaOne_two_pow_mul_odd_prime {k p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    sigmaOne (2 ^ k * p) + (p + 1) = 2 ^ (k + 1) * (p + 1) := by
  have hcop : Nat.Coprime (2 ^ k) p :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have h := sigmaOne_two_pow k
  rw [sigmaOne_mul_of_coprime hcop, sigmaOne_prime hp]
  nlinarith [h]

/-- Unique-partner theorem: if `m` is betrothed to `2^k p` with `p` an odd prime,
then `m = (2^k - 1)(p + 2)`.  (No lower bound on `k` is needed.) -/
