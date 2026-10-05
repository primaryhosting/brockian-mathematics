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

lemma prod_le_of_card_le_three (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hcard : S.card ≤ 3) :
    ∏ p ∈ S, (p : ℤ) ≤ 4 * ∏ p ∈ S, ((p : ℤ) - 1) := by
  interval_cases h : S.card
  · rw [Finset.card_eq_zero] at h
    subst h
    simp
  · rw [Finset.card_eq_one] at h
    obtain ⟨a, rfl⟩ := h
    simp only [Finset.prod_singleton]
    exact one_bound (prime_cast_cases (hS a (by simp)))
  · rw [Finset.card_eq_two] at h
    obtain ⟨a, b, hab, rfl⟩ := h
    rw [Finset.prod_pair hab, Finset.prod_pair hab]
    exact two_bound (prime_cast_cases (hS a (by simp))) (prime_cast_cases (hS b (by simp)))
      (by exact_mod_cast hab)
  · rw [Finset.card_eq_three] at h
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := h
    rw [Finset.prod_insert (by simp [hab, hac]), Finset.prod_pair hbc,
      Finset.prod_insert (by simp [hab, hac]), Finset.prod_pair hbc]
    exact three_bound (prime_cast_cases (hS a (by simp))) (prime_cast_cases (hS b (by simp)))
      (prime_cast_cases (hS c (by simp))) (by exact_mod_cast hab) (by exact_mod_cast hac)
      (by exact_mod_cast hbc)

/-- `σ (p ^ k) * (p - 1) = p ^ (k + 1) - 1` for a prime `p`. -/
