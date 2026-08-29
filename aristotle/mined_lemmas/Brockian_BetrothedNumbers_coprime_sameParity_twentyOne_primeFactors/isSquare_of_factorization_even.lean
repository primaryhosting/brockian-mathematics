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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- A *betrothed* (quasi-amicable) pair: two positive integers, each of whose
divisor sums equals the sum of the pair plus one. -/

lemma isSquare_of_factorization_even {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p ∈ n.primeFactors, Even (n.factorization p)) : IsSquare n := by
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  refine Finset.prod_congr rfl ?_
  intro p hp
  rw [← pow_add]
  congr 1
  obtain ⟨c, hc⟩ := h p hp
  omega

/-- For an odd positive integer `n`, the divisor sum `σ(n)` is odd if and only if
`n` is a perfect square. -/
