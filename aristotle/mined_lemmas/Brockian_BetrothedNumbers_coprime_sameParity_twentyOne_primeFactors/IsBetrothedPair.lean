import Mathlib

/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Nat

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-! ## The definition -/

/-- A *betrothed* (quasi-amicable) pair: two positive integers each of whose sum of
divisors equals the sum of the two numbers plus one, i.e. `σ₁(m) = σ₁(n) = m + n + 1`. -/

def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

/-- The rational abundancy bound `∏_{p ∣ n} p/(p-1)`, an upper bound for `σ₁(n)/n`. -/
