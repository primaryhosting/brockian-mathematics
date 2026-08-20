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

lemma sigma_one_le_mul_abundancyBound {n : ℕ} (hn : n ≠ 0) :
    (sigma 1 n : ℚ) ≤ n * abundancyBound n := by
  have hcast : ((sigma 1 n : ℕ) : ℚ)
      = ∏ p ∈ n.primeFactors, (∑ i ∈ Finset.range (n.factorization p + 1), (p : ℚ) ^ i) := by
    rw [sigma_one_apply, Nat.sum_divisors hn]
    push_cast
    ring
  have hself : (n : ℚ) = ∏ p ∈ n.primeFactors, (p : ℚ) ^ (n.factorization p) := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Finsupp.prod, Nat.support_factorization]
    push_cast
    ring
  rw [hcast, abundancyBound, hself, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun p _ => ?_) (fun p hp => ?_)
  · positivity
  · exact geom_sum_le_pow_mul (Nat.prime_of_mem_primeFactors hp).two_le _

/-- The abundancy bound is multiplicative on coprime arguments. -/
