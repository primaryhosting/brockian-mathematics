/-
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open Finset
open scoped ArithmeticFunction.sigma

namespace Brockian
namespace BetrothedNumbers

/-!
## Betrothed (quasi-amicable) pairs

A pair `(m, n)` of positive integers is *betrothed* (also called *quasi-amicable*, or a
*reduced amicable pair*) when each of the two numbers is the sum of the *nontrivial* proper
divisors of the other, i.e. `σ₁ m = σ₁ n = m + n + 1`.
-/

/-- `Betrothed m n` says that `(m, n)` is a betrothed (quasi-amicable) pair:
the sum of divisors of each of `m` and `n` equals `m + n + 1`. -/

theorem twentyOne_primeFactors_of_abundancy_gt_four {N : ℕ} (hN : N ≠ 0) (hodd : Odd N)
    (habund : 4 < (σ 1 N : ℚ) / N) : 21 ≤ N.primeFactors.card := by
  by_contra hcon
  have hcard : N.primeFactors.card ≤ 20 := by omega
  have hS : ∀ p ∈ N.primeFactors, p.Prime ∧ p ≠ 2 := by
    intro p hp
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    rintro rfl
    have h2 : 2 ∣ N := Nat.dvd_of_mem_primeFactors hp
    rw [Nat.odd_iff] at hodd
    omega
  have h1 := abundancy_le_prod_primeFactors hN
  have h2 := prod_ratio_le_of_card_le hS hcard
  have h3 := prod_smallOddPrimes_lt_four
  linarith

/-!
## The main theorem
-/

/-- **Second part of Hagis–Lord, Proposition 2.**
If `(m, n)` is a betrothed (quasi-amicable) pair with `gcd m n = 1` whose members have the same
parity, then both members are odd, each of them is a perfect square, and the product `m * n`
has at least twenty-one distinct prime factors. -/
