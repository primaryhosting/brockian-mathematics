import Mathlib

/-!
# Coprime Pair Four Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_pair_four_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ArithmeticFunction.sigma

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Finset ArithmeticFunction

/-- A pair `(m, n)` of *betrothed* (a.k.a. quasi-amicable) numbers: each of the two numbers
is the sum of the *nontrivial* proper divisors of the other, i.e.
`σ m = m + n + 1` and `σ n = m + n + 1`.  As is customary the two members of the pair are
required to be distinct (this hypothesis is not needed for the theorem below). -/

lemma sigma_primePow_mul_sub_one {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ((σ 1 (p ^ k) : ℕ) : ℤ) * ((p : ℤ) - 1) = (p : ℤ) ^ (k + 1) - 1 := by
  have : σ 1 (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
    rw [sigma_one_apply, Nat.sum_divisors_prime_pow hp]
  rw [this]
  push_cast
  rw [geom_sum_mul]

/-- The key inequality: `σ N * ∏_{p ∣ N} (p - 1) < N * ∏_{p ∣ N} p` for `N > 1`. -/
