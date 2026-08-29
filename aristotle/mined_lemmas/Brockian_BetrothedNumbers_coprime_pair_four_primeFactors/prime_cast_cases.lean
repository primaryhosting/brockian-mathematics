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

lemma prime_cast_cases {p : ℕ} (hp : p.Prime) : (p : ℤ) = 2 ∨ (p : ℤ) = 3 ∨ 5 ≤ (p : ℤ) := by
  have h2 : 2 ≤ p := hp.two_le
  rcases eq_or_lt_of_le h2 with h | h
  · exact Or.inl (by exact_mod_cast h.symm)
  have h3' : 3 ≤ p := h
  rcases eq_or_lt_of_le h3' with h3 | h3
  · exact Or.inr (Or.inl (by exact_mod_cast h3.symm))
  -- now `3 < p`, and `p ≠ 4` since `4` is not prime
  have h4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  have : 5 ≤ p := by omega
  exact Or.inr (Or.inr (by exact_mod_cast this))

/-- Bound for a single prime. -/
