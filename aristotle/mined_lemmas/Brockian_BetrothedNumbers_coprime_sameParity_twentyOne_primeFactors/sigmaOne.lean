/-
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Finset

/-! ## Basic definitions -/

/-- `sigmaOne n` is the sum-of-divisors function `σ₁(n) = ∑_{d ∣ n} d`. -/

def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- A *betrothed pair* (quasi-amicable pair): two distinct positive integers each of whose
divisor sums equals `m + n + 1`, i.e. the sum of the proper divisors of each (excluding `1`
and the number itself) equals the other. -/
