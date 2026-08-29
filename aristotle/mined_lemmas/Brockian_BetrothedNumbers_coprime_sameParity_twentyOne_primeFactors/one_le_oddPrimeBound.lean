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

lemma one_le_oddPrimeBound (k : ℕ) : 1 ≤ oddPrimeBound k :=
  Finset.one_le_prod _ (fun _ => one_le_abFactor (Nat.prime_nth_prime _).two_le)

