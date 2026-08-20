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

lemma sigmaOne_prime_sq {q : ℕ} (hq : q.Prime) : sigmaOne (q ^ 2) = 1 + q + q ^ 2 := by
  rw [sigmaOne_eq_sigma, sigma_one_apply_prime_pow hq]
  simp [Finset.sum_range_succ, sq]

