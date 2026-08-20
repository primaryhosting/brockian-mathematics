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

theorem prod_ratio_le_of_card_le {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) (hcard : S.card ≤ 20) :
    ∏ p ∈ S, (p : ℚ) / (p - 1) ≤ ∏ p ∈ smallOddPrimes, (p : ℚ) / (p - 1) := by
  classical
  have key1 : ∏ p ∈ S \ smallOddPrimes, (p : ℚ) / (p - 1)
      ≤ (79 / 78 : ℚ) ^ ((S \ smallOddPrimes).card) := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have h2 := (hS p (Finset.mem_sdiff.mp hp).1).1.two_le
      have h2' : (2 : ℚ) ≤ p := by exact_mod_cast h2
      have h1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
      positivity
    · obtain ⟨hpS, hpT⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hprime, hne⟩ := hS p hpS
      have h79 : 79 ≤ p := by
        by_contra hcon
        exact hpT (mem_smallOddPrimes hprime hne (by omega))
      have h79' : (79 : ℚ) ≤ p := by exact_mod_cast h79
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
  have key2 : ((73 : ℚ) / 72) ^ ((smallOddPrimes \ S).card)
      ≤ ∏ p ∈ smallOddPrimes \ S, (p : ℚ) / (p - 1) := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod (fun p _ => by norm_num) (fun p hp => ?_)
    obtain ⟨h3, h73⟩ := smallOddPrimes_bounds p (Finset.mem_sdiff.mp hp).1
    have h3' : (3 : ℚ) ≤ p := by exact_mod_cast h3
    have h73' : (p : ℚ) ≤ 73 := by exact_mod_cast h73
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]
    linarith
  have hcards : (S \ smallOddPrimes).card ≤ (smallOddPrimes \ S).card := by
    have h1 := Finset.card_sdiff_add_card_inter S smallOddPrimes
    have h2 := Finset.card_sdiff_add_card_inter smallOddPrimes S
    have h3 : (S ∩ smallOddPrimes).card = (smallOddPrimes ∩ S).card := by rw [Finset.inter_comm]
    have h4 := card_smallOddPrimes
    omega
  have step : (79 / 78 : ℚ) ^ ((S \ smallOddPrimes).card)
      ≤ (73 / 72 : ℚ) ^ ((smallOddPrimes \ S).card) :=
    le_trans (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
      (pow_le_pow_right₀ (by norm_num) hcards)
  have hpos : (0 : ℚ) < ∏ p ∈ S ∩ smallOddPrimes, (p : ℚ) / (p - 1) := by
    refine Finset.prod_pos (fun p hp => ?_)
    have h2 := (hS p (Finset.mem_inter.mp hp).1).1.two_le
    have h2' : (2 : ℚ) ≤ p := by exact_mod_cast h2
    have h1 : (0 : ℚ) < (p : ℚ) - 1 := by linarith
    positivity
  calc ∏ p ∈ S, (p : ℚ) / (p - 1)
      = (∏ p ∈ S ∩ smallOddPrimes, (p : ℚ) / (p - 1))
        * ∏ p ∈ S \ smallOddPrimes, (p : ℚ) / (p - 1) :=
        (Finset.prod_inter_mul_prod_diff S smallOddPrimes _).symm
    _ ≤ (∏ p ∈ S ∩ smallOddPrimes, (p : ℚ) / (p - 1))
        * ∏ p ∈ smallOddPrimes \ S, (p : ℚ) / (p - 1) := by
        refine mul_le_mul_of_nonneg_left ?_ hpos.le
        exact le_trans key1 (le_trans step key2)
    _ = (∏ p ∈ smallOddPrimes ∩ S, (p : ℚ) / (p - 1))
        * ∏ p ∈ smallOddPrimes \ S, (p : ℚ) / (p - 1) := by rw [Finset.inter_comm]
    _ = ∏ p ∈ smallOddPrimes, (p : ℚ) / (p - 1) :=
        Finset.prod_inter_mul_prod_diff smallOddPrimes S _

