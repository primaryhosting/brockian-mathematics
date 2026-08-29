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

namespace Brockian.BetrothedNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- A *betrothed* (quasi-amicable) pair: two positive integers, each of whose sum of
divisors equals their sum plus one. -/

lemma prod_ratio_lt_four_of_card_le_twenty {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (hcard : S.card ≤ 20) :
    ∏ p ∈ S, (p : ℚ) / (p - 1) < 4 := by
  refine lt_of_le_of_lt ?_ prod_oddPrimes20_lt_four
  refine prod_ratio_le_list oddPrimes20 chain_oddPrimes20 (by decide) S
    (fun p hp => (hS p hp).1) ?_ (by simpa [oddPrimes20] using hcard)
  intro a ha p hp
  have ha3 : a = 3 := by simpa [oddPrimes20] using ha.symm
  subst ha3
  obtain ⟨hpp, hp2⟩ := hS p hp
  have := hpp.two_le
  omega

/-! ### The main theorem -/

/-- **Hagis–Lord, Proposition 2 (second part).**  If a betrothed (quasi-amicable) pair
`(m, n)` is coprime and its two members have the same parity, then both members are odd
and the product `m * n` has at least twenty-one distinct prime factors.

The proof is exact: coprimality forces `σ₁(m * n) = σ₁(m) σ₁(n) = (m + n + 1)^2 > 4 m n`,
i.e. `m * n` is an odd number of abundancy greater than `4`, while the product
`∏_{p ∣ m n} p/(p-1)` taken over at most twenty odd primes is smaller than `4`. -/
