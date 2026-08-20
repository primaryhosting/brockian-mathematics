import Mathlib
import RequestProject.Brun.Final

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

lemma sum_inv_primes_block_le {j : ℕ} (hj : 1 ≤ j) :
    ∑ p ∈ (range (2 ^ (j + 1) + 1)).filter (fun p => Nat.Prime p ∧ 2 ^ j < p), (1 / (p : ℝ))
      ≤ 4 / j := by
  set B := (range (2 ^ (j + 1) + 1)).filter (fun p => Nat.Prime p ∧ 2 ^ j < p) with hB
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have h1 : ∑ p ∈ B, (1 / (p : ℝ)) ≤ ∑ _p ∈ B, (1 / (2 ^ j : ℝ)) := by
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hp2 : 2 ^ j < p := (Finset.mem_filter.mp hp).2.2
    have hpR : ((2 : ℝ) ^ j) ≤ (p : ℝ) := by
      have : ((2 ^ j : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2.le
      simpa using this
    exact one_div_le_one_div_of_le (by positivity) hpR
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  have hcard := card_primes_block_mul_le j
  have hcardR : (B.card : ℝ) * (j : ℝ) ≤ (2 : ℝ) ^ (j + 2) := by
    have : ((B.card * j : ℕ) : ℝ) ≤ ((2 ^ (j + 2) : ℕ) : ℝ) := by exact_mod_cast hcard
    push_cast at this
    linarith
  have h2 : (B.card : ℝ) * (1 / (2 ^ j : ℝ)) ≤ 4 / j := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hjR]
    have : (2 : ℝ) ^ (j + 2) = 4 * 2 ^ j := by ring
    nlinarith [hcardR]
  linarith

/-- `∑_{p ≤ 2^q} 1/p ≤ 5 + 4 log q`. -/
