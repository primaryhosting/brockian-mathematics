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

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- `Betrothed m n` says that `(m, n)` is a betrothed (quasi-amicable) pair:
both are positive and `σ m = σ n = m + n + 1`. -/

lemma sigma_one_le_mul_prod_primeRatio {n : ℕ} (hn : n ≠ 0) :
    (σ 1 n : ℚ) ≤ (n : ℚ) * ∏ p ∈ n.primeFactors, primeRatio p := by
  have hnfac : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p :=
    (Nat.factorization_prod_pow_eq_self hn).symm
  have hsig : σ 1 n = ∏ p ∈ n.primeFactors, ∑ k ∈ range (n.factorization p + 1), p ^ k := by
    rw [sigma_one_apply]; exact Nat.sum_divisors hn
  rw [hsig]
  have hcast : ((∏ p ∈ n.primeFactors, ∑ k ∈ range (n.factorization p + 1), p ^ k : ℕ) : ℚ)
      = ∏ p ∈ n.primeFactors, ((∑ k ∈ range (n.factorization p + 1), p ^ k : ℕ) : ℚ) := by
    push_cast; ring
  rw [hcast]
  have hRHS : (n : ℚ) * ∏ p ∈ n.primeFactors, primeRatio p
      = ∏ p ∈ n.primeFactors, ((p : ℚ) ^ n.factorization p * primeRatio p) := by
    rw [Finset.prod_mul_distrib]
    congr 1
    calc (n : ℚ) = ((∏ p ∈ n.primeFactors, p ^ n.factorization p : ℕ) : ℚ) := by
            exact_mod_cast congrArg (Nat.cast : ℕ → ℚ) hnfac
      _ = ∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p := by push_cast; ring
  rw [hRHS]
  refine Finset.prod_le_prod (fun p _ => by positivity) (fun p hp => ?_)
  exact sigma_primePow_le (Nat.prime_of_mem_primeFactors hp).two_le _

/-! ## Parity of `σ`

The classical characterisation `σ n` odd ↔ `n` a square (for odd `n`), used to see that the
members of a coprime same-parity betrothed pair are perfect squares. -/

/-- For odd `p`, the geometric sum `1 + p + ⋯ + p ^ (m-1)` has the same parity as `m`. -/
