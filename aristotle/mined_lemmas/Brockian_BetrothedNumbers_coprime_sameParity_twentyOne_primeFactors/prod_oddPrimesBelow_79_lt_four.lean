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

lemma prod_oddPrimesBelow_79_lt_four : ∏ q ∈ oddPrimesBelow 79, primeRatio q < 4 := by
  rw [oddPrimesBelow_79]
  have hdiv : ∏ p ∈ T20, primeRatio p = (∏ p ∈ T20, (p : ℚ)) / ∏ p ∈ T20, ((p : ℚ) - 1) := by
    rw [← Finset.prod_div_distrib]; rfl
  have hpos : (0 : ℚ) < ∏ p ∈ T20, ((p : ℚ) - 1) := by
    apply Finset.prod_pos
    intro p hp
    have h3 : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast three_le_of_mem_T20 p hp
    linarith
  rw [hdiv, div_lt_iff₀ hpos]
  have hcast1 : (∏ p ∈ T20, (p : ℚ)) = ((∏ p ∈ T20, p : ℕ) : ℚ) := by push_cast; ring
  have hcast2 : (∏ p ∈ T20, ((p : ℚ) - 1)) = ((∏ p ∈ T20, (p - 1) : ℕ) : ℚ) := by
    rw [Nat.cast_prod]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have h1 : 1 ≤ p := le_trans (by norm_num) (three_le_of_mem_T20 p hp)
    rw [Nat.cast_sub h1, Nat.cast_one]
  rw [hcast1, hcast2]
  have hnat : ((∏ p ∈ T20, p : ℕ) : ℚ) < ((4 * ∏ p ∈ T20, (p - 1) : ℕ) : ℚ) := by
    exact_mod_cast prod_T20_lt_four_prod_pred
  push_cast at hnat ⊢
  linarith

/-- Any set of at most twenty odd primes has `∏ p/(p-1) < 4`. -/
