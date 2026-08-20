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

theorem isSquare_iff_even_factorization {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p ∈ n.primeFactors, Even (n.factorization p) := by
  constructor
  · rintro ⟨r, rfl⟩ p _
    have hr : r ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.factorization_mul hr hr]
    simp
  · intro h
    refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
    rw [← Finset.prod_mul_distrib]
    conv_lhs =>
      rw [← Nat.factorization_prod_pow_eq_self hn, Finsupp.prod, Nat.support_factorization]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    obtain ⟨k, hk⟩ := h p hp
    rw [hk, ← pow_add]
    congr 1
    omega

/-- A product of natural numbers is odd iff each factor is odd. -/
