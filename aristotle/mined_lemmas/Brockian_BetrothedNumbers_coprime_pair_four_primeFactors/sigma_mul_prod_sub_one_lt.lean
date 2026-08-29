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

lemma sigma_mul_prod_sub_one_lt {N : ℕ} (hN : 1 < N) :
    ((σ 1 N : ℕ) : ℤ) * ∏ p ∈ N.primeFactors, ((p : ℤ) - 1)
      < (N : ℤ) * ∏ p ∈ N.primeFactors, (p : ℤ) := by
  have hN0 : N ≠ 0 := by omega
  have hσ : ((σ 1 N : ℕ) : ℤ)
      = ∏ p ∈ N.primeFactors, ((σ 1 (p ^ N.factorization p) : ℕ) : ℤ) := by
    have := ArithmeticFunction.IsMultiplicative.multiplicative_factorization
      (σ 1) ArithmeticFunction.isMultiplicative_sigma hN0
    rw [this, Finsupp.prod, Nat.support_factorization, Nat.cast_prod]
  have hNe : (N : ℤ) = ∏ p ∈ N.primeFactors, (p : ℤ) ^ N.factorization p := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hN0]
    rw [Finsupp.prod, Nat.support_factorization, Nat.cast_prod]
    push_cast
    rfl
  rw [hσ, hNe, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_lt_prod_of_nonempty ?_ ?_ (Nat.nonempty_primeFactors.2 hN)
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have h2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hpp.two_le
    have hσpos : (0 : ℤ) < ((σ 1 (p ^ N.factorization p) : ℕ) : ℤ) := by
      have : 0 < σ 1 (p ^ N.factorization p) :=
        ArithmeticFunction.sigma_pos 1 _ (pow_ne_zero _ hpp.pos.ne')
      exact_mod_cast this
    have : (0 : ℤ) < (p : ℤ) - 1 := by linarith
    positivity
  · intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [sigma_primePow_mul_sub_one hpp]
    have : (p : ℤ) ^ N.factorization p * (p : ℤ) = (p : ℤ) ^ (N.factorization p + 1) := by
      ring
    rw [this]
    linarith

/-- **Hagis–Lord, Proposition 2.**  If `m` and `n` are coprime betrothed numbers then
`m * n` has at least four distinct prime factors. -/
