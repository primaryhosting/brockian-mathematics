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
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Finset

/-- Notation for the sum-of-divisors function `σ₁`. -/
local notation "σ₁" => ArithmeticFunction.sigma 1

/-! ## Definition -/

/-- A *betrothed* (or *quasi-amicable*) pair: two positive integers each of whose
sum of divisors equals the sum of the two numbers plus one. -/

theorem card_primeFactors_of_odd_of_four_mul_lt_sigma {N : ℕ} (hN : 0 < N) (hodd : Odd N)
    (habund : 4 * N < σ₁ N) : 21 ≤ N.primeFactors.card := by
  by_contra hcon
  push_neg at hcon
  have hcard : N.primeFactors.card ≤ 20 := by omega
  have hS : ∀ p ∈ N.primeFactors, p.Prime ∧ p ≠ 2 := by
    intro p hp
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    rintro rfl
    have h2 : (2 : ℕ) ∣ N := Nat.dvd_of_mem_primeFactors hp
    rw [Nat.odd_iff] at hodd
    omega
  -- the rational bound
  have hQ := prod_ratio_lt_four N.primeFactors hS hcard
  -- transfer to natural numbers
  set Q : ℕ := ∏ p ∈ N.primeFactors, p with hQdef
  set D : ℕ := ∏ p ∈ N.primeFactors, (p - 1) with hDdef
  have hDpos : 0 < D := by
    refine Finset.prod_pos ?_
    intro p hp
    have := (hS p hp).1.two_le
    omega
  have hcastD : (D : ℚ) = ∏ p ∈ N.primeFactors, ((p : ℚ) - 1) := by
    rw [hDdef, Nat.cast_prod]
    refine Finset.prod_congr rfl ?_
    intro p hp
    have := (hS p hp).1.two_le
    push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
    ring
  have hcastQ : (Q : ℚ) = ∏ p ∈ N.primeFactors, (p : ℚ) := by rw [hQdef, Nat.cast_prod]
  have hne : ∀ p ∈ N.primeFactors, ((p : ℚ) - 1) ≠ 0 := by
    intro p hp
    have := (hS p hp).1.two_le
    have : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast this
    intro h; linarith
  have hprod_div : ∏ p ∈ N.primeFactors, ((p : ℚ) / (p - 1)) = (Q : ℚ) / (D : ℚ) := by
    rw [hcastQ, hcastD, ← Finset.prod_div_distrib]
  have hDQ : (Q : ℚ) < 4 * (D : ℚ) := by
    have hDpos' : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hDpos
    rw [hprod_div, div_lt_iff₀ hDpos'] at hQ
    linarith
  have hQD : Q < 4 * D := by exact_mod_cast hDQ
  -- contradiction
  have e1 : 4 * N * D < σ₁ N * D := by
    exact Nat.mul_lt_mul_of_lt_of_le habund (le_refl D) hDpos
  have e2 : σ₁ N * D ≤ N * Q := sigma_mul_prod_pred_le (by omega)
  have e3 : N * Q < N * (4 * D) := Nat.mul_lt_mul_of_pos_left hQD hN
  have e4 : N * (4 * D) = 4 * N * D := by ring
  omega

/-! ## Parity of `σ₁` and squares -/

/-- For an odd prime `p`, `σ₁ (p ^ a) ≡ a + 1 [MOD 2]`. -/
