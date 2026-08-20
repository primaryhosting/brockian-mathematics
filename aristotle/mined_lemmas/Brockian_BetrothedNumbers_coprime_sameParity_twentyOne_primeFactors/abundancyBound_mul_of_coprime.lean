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

lemma abundancyBound_mul_of_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : Nat.Coprime m n) :
    abundancyBound (m * n) = abundancyBound m * abundancyBound n := by
  rw [abundancyBound, abundancyBound, abundancyBound, Nat.primeFactors_mul hm hn,
    Finset.prod_union h.disjoint_primeFactors]

/-! ## The numerical bound: twenty odd primes are not enough -/

/-- The twenty smallest odd primes, i.e. all odd primes below `79`. -/
