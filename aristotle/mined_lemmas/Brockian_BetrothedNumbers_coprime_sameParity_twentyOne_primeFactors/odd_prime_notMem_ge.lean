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

theorem odd_prime_notMem_ge {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (h : p ∉ firstTwentyOddPrimes) : 79 ≤ p := by
  by_contra hlt
  push_neg at hlt
  have key : ∀ q < 79, Nat.Prime q → q % 2 = 1 → q ∈ firstTwentyOddPrimes := by decide
  exact h (key p hlt hp (Nat.odd_iff.mp hodd))

/-- If `S` is a set of at most twenty odd primes, then `∏_{p ∈ S} p / (p - 1) < 4`.

The proof compares `S` with the set `Q` of the first twenty odd primes: the factors coming
from primes of `S` outside `Q` are each at most `79 / 78`, and there are enough spare
factors in `Q \ S`, each at least `79 / 78`, to absorb them. -/
