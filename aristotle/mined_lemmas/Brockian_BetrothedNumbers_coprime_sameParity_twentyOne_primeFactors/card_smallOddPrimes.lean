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

theorem card_smallOddPrimes : smallOddPrimes.card = 20 := by decide

