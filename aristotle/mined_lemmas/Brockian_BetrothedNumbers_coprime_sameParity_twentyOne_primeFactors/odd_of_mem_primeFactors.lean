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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- A *betrothed* (quasi-amicable) pair: two positive integers, each of whose
divisor sums equals the sum of the pair plus one. -/

lemma odd_of_mem_primeFactors {N p : ℕ} (hodd : Odd N) (hp : p ∈ N.primeFactors) : Odd p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hdvd := Nat.dvd_of_mem_primeFactors hp
  refine hpp.odd_of_ne_two ?_
  rintro rfl
  obtain ⟨c, rfl⟩ := hdvd
  have := Nat.odd_iff.mp hodd
  omega

