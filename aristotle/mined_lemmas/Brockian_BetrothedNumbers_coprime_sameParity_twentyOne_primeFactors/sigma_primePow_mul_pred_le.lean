import Mathlib

/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Finset

/-- Notation for the sum-of-divisors function `σ₁`. -/
local notation "σ₁" => ArithmeticFunction.sigma 1

/-! ## Definition -/

/-- A *betrothed* (or *quasi-amicable*) pair: two positive integers each of whose
sum of divisors equals the sum of the two numbers plus one. -/

lemma sigma_primePow_mul_pred_le (p a : ℕ) (hp : p.Prime) :
    σ₁ (p ^ a) * (p - 1) ≤ p ^ (a + 1) := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  have h2 := hp.two_le
  induction a with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      calc (∑ x ∈ Finset.range (k + 1), p ^ x + p ^ (k + 1)) * (p - 1)
          = (∑ x ∈ Finset.range (k + 1), p ^ x) * (p - 1) + p ^ (k + 1) * (p - 1) := by ring
        _ ≤ p ^ (k + 1) + p ^ (k + 1) * (p - 1) := Nat.add_le_add_right ih _
        _ = p ^ (k + 1) * (1 + (p - 1)) := by ring
        _ = p ^ (k + 1) * p := by congr 1; omega
        _ = p ^ (k + 1 + 1) := by ring

/-- The integral form of the abundancy bound:
`σ₁ n * ∏_{p ∣ n} (p - 1) ≤ n * ∏_{p ∣ n} p`. -/
