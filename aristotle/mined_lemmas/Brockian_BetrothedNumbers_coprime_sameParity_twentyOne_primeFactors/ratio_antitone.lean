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

lemma ratio_antitone {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (b : ℚ) / (b - 1) ≤ (a : ℚ) / (a - 1) := by
  have ha' : (2 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha
  have hab' : (a : ℚ) ≤ (b : ℚ) := by exact_mod_cast hab
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Every odd prime below `79` is one of the twenty smallest odd primes. -/
