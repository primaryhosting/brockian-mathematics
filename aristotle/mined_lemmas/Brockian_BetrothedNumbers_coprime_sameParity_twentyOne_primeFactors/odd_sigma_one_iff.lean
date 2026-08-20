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

theorem odd_sigma_one_iff {n : ℕ} (hn : n ≠ 0) (hodd : Odd n) :
    Odd (σ 1 n) ↔ IsSquare n := by
  have hoddp : ∀ p ∈ n.primeFactors, p % 2 = 1 := by
    intro p hp
    have hpd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    rcases (Nat.prime_of_mem_primeFactors hp).eq_two_or_odd with h2 | h1
    · subst h2
      rw [Nat.odd_iff] at hodd
      omega
    · exact h1
  have hfac : σ 1 n
      = ∏ p ∈ n.primeFactors, ∑ k ∈ Finset.range (n.factorization p + 1), p ^ k := by
    rw [ArithmeticFunction.sigma_one_apply, Nat.sum_divisors hn]
  rw [hfac, odd_prod_iff, isSquare_iff_even_factorization hn]
  exact forall₂_congr fun p hp => odd_geom_sum_iff (hoddp p hp)

/-!
## The rational abundancy bound
-/

/-- For a prime `p`, the abundancy contribution of `p ^ a` is at most `p / (p - 1)`. -/
