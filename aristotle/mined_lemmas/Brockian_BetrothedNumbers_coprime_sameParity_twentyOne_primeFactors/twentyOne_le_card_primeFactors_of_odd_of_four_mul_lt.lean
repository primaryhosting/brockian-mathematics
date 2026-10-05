/-
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Finset

/-! ## Basic definitions -/

/-- `sigmaOne n` is the sum-of-divisors function `σ₁(n) = ∑_{d ∣ n} d`. -/

lemma twentyOne_le_card_primeFactors_of_odd_of_four_mul_lt
    {N : ℕ} (hN : N ≠ 0) (hodd : Odd N) (h4 : 4 * N < sigmaOne N) :
    21 ≤ N.primeFactors.card := by
  by_contra hcon
  push_neg at hcon
  have hcard : N.primeFactors.card ≤ oddPrimes20.length := by
    simp only [oddPrimes20, List.length_cons, List.length_nil]
    omega
  have hprime : ∀ p ∈ N.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hthree : ∀ p ∈ N.primeFactors, 3 ≤ p := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd : p ∣ N := Nat.dvd_of_mem_primeFactors hp
    have hne : p ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
    have := hpp.two_le
    omega
  have hbound : ∏ p ∈ N.primeFactors, w p ≤ (oddPrimes20.map w).prod := by
    refine prod_w_le_of_gapChain oddPrimes20 N.primeFactors (by intro b hb; fin_cases hb <;> norm_num)
      oddPrimes20_gapChain hprime ?_ hcard
    intro b hb p hp
    simp only [oddPrimes20, List.head?_cons, Option.mem_def, Option.some.injEq] at hb
    subst hb
    exact hthree p hp
  have hNpos : (0:ℚ) < (N:ℚ) := by
    have : 0 < N := Nat.pos_of_ne_zero hN
    exact_mod_cast this
  have hle := sigmaOne_le_mul_prod_w N hN
  have hlt : (sigmaOne N : ℚ) < 4 * (N:ℚ) := by
    calc (sigmaOne N : ℚ) ≤ (N : ℚ) * ∏ p ∈ N.primeFactors, w p := hle
      _ ≤ (N : ℚ) * (oddPrimes20.map w).prod := by
          exact mul_le_mul_of_nonneg_left hbound (le_of_lt hNpos)
      _ < (N : ℚ) * 4 := by
          exact mul_lt_mul_of_pos_left prod_map_w_oddPrimes20_lt_four hNpos
      _ = 4 * (N:ℚ) := by ring
  have h4' : (4 * N : ℚ) < (sigmaOne N : ℚ) := by exact_mod_cast h4
  push_cast at h4'
  linarith

/-! ## Parity of the divisor sum: `odd_sigma_one_iff` -/

/-- A nonzero natural number is a perfect square iff every exponent in its prime
factorization is even. -/
