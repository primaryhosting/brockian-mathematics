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

lemma four_mul_lt_sigma_mul {m n : ℕ} (h : IsBetrothedPair m n) (hcop : Nat.Coprime m n) :
    4 * (m * n) < σ₁ (m * n) := by
  obtain ⟨-, -, hm, hn⟩ := h
  have hmul : σ₁ (m * n) = σ₁ m * σ₁ n :=
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop
  rw [hmul, hm, hn]
  nlinarith [two_mul_le_add_sq m n, sq_nonneg (m + n)]

/-- **Hagis–Lord, Proposition 2 (second part).**
If `(m, n)` is a betrothed (quasi-amicable) pair which is coprime and whose two members have
the same parity, then both members are odd and the product `m * n` has at least twenty-one
distinct prime factors.

This is an exact, unconditional theorem.  It should not be confused with the *computational*
lower bounds attached to the same problem in the literature (for instance the statements that
a same-parity betrothed pair, if any exists, must exceed certain explicit numerical bounds):
those come from finite machine searches and are not formalized here. -/
