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

namespace Brockian
namespace BetrothedNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-! ## Betrothed (quasi-amicable) pairs -/

/-- A *betrothed* (quasi-amicable) pair: two positive integers each of whose sum of
divisors equals `m + n + 1`; equivalently `s(m) = n + 1` and `s(n) = m + 1`, where `s`
denotes the sum of the proper divisors. -/

theorem prod_firstTwentyOddPrimes_lt_four :
    (∏ p ∈ firstTwentyOddPrimes, (p : ℚ) / ((p : ℚ) - 1)) < 4 := by
  rw [show firstTwentyOddPrimes =
      (⟨[3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73],
        by decide⟩ : Finset ℕ) from by decide, Finset.prod_mk]
  norm_num [Multiset.prod_coe]

/-- An odd prime that is not among the first twenty odd primes is at least `79`. -/
