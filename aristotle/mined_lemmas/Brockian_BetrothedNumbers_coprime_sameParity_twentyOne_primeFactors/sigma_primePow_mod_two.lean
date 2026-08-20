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

lemma sigma_primePow_mod_two {p : ℕ} (a : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    σ₁ (p ^ a) % 2 = (a + 1) % 2 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  induction a with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, Nat.add_mod, ih]
      have hpk : p ^ (k + 1) % 2 = 1 := by rw [Nat.pow_mod, hodd]; simp
      omega

/-- A positive natural number is a square exactly when all exponents in its prime
factorization are even. -/
