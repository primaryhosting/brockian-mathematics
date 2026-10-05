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

lemma prod_abFactor_lt_four (S : Finset ℕ) (hp : ∀ p ∈ S, p.Prime) (h3 : ∀ p ∈ S, 3 ≤ p)
    (hcard : S.card ≤ 20) : ∏ p ∈ S, abFactor p < 4 :=
  lt_of_le_of_lt ((prod_abFactor_le_bound S.card S rfl hp h3).trans
    (oddPrimeBound_mono hcard)) oddPrimeBound_twenty_lt_four

/-! ## Odd `4`-abundant numbers have at least twenty-one prime factors -/

