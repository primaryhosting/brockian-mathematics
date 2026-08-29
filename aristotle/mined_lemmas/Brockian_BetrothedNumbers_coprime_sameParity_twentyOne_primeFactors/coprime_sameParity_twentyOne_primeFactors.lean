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

namespace Brockian.BetrothedNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- A *betrothed* (quasi-amicable) pair: two positive integers, each of whose sum of
divisors equals their sum plus one. -/

theorem coprime_sameParity_twentyOne_primeFactors {m n : ℕ} (h : Betrothed m n)
    (hcop : Nat.Coprime m n) (hpar : m % 2 = n % 2) :
    Odd m ∧ Odd n ∧ 21 ≤ (m * n).primeFactors.card := by
  obtain ⟨hm0, hn0, hsm, hsn⟩ := h
  -- Coprimality plus equal parity forces both members to be odd.
  have hmodd : m % 2 = 1 := by
    by_contra hc
    have hm2 : (2 : ℕ) ∣ m := Nat.dvd_of_mod_eq_zero (by omega)
    have hn2 : (2 : ℕ) ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
    have hdvd : (2 : ℕ) ∣ Nat.gcd m n := Nat.dvd_gcd hm2 hn2
    rw [Nat.Coprime] at hcop
    omega
  have hnodd : n % 2 = 1 := by omega
  refine ⟨Nat.odd_iff.mpr hmodd, Nat.odd_iff.mpr hnodd, ?_⟩
  by_contra hcontra
  push_neg at hcontra
  have hcard : (m * n).primeFactors.card ≤ 20 := by omega
  have hN0 : m * n ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  -- every prime factor of `m * n` is odd
  have hodd : ∀ p ∈ (m * n).primeFactors, p.Prime ∧ p ≠ 2 := by
    intro p hp
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    rintro rfl
    have hdvd : (2 : ℕ) ∣ m * n := Nat.dvd_of_mem_primeFactors hp
    have : (m * n) % 2 = 1 := by
      rw [Nat.mul_mod, hmodd, hnodd]
    omega
  -- the sum of divisors of the product
  have hmul : σ 1 (m * n) = (m + n + 1) * (m + n + 1) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsm, hsn]
  have hbound := sigma_one_le_mul_prod_primeFactors (N := m * n) hN0
  have hlt := prod_ratio_lt_four_of_card_le_twenty hodd hcard
  rw [hmul] at hbound
  have hmnpos : (0 : ℚ) < (m : ℚ) * n := by
    have : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm0
    have : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn0
    positivity
  have hupper : ((m : ℚ) + n + 1) * ((m : ℚ) + n + 1) < 4 * ((m : ℚ) * n) := by
    have hcast : (((m + n + 1) * (m + n + 1) : ℕ) : ℚ)
        = ((m : ℚ) + n + 1) * ((m : ℚ) + n + 1) := by push_cast; ring
    have h1 : ((m : ℚ) + n + 1) * ((m : ℚ) + n + 1)
        ≤ ((m * n : ℕ) : ℚ) * ∏ p ∈ (m * n).primeFactors, (p : ℚ) / (p - 1) := by
      rw [← hcast]; exact hbound
    have h2 : ((m * n : ℕ) : ℚ) * ∏ p ∈ (m * n).primeFactors, (p : ℚ) / (p - 1)
        < ((m * n : ℕ) : ℚ) * 4 := by
      refine mul_lt_mul_of_pos_left hlt ?_
      push_cast
      exact hmnpos
    push_cast at h1 h2 ⊢
    linarith
  -- but `(m + n + 1)^2 > (m + n)^2 ≥ 4 m n`
  have hAMGM : 4 * ((m : ℚ) * n) ≤ ((m : ℚ) + n) * ((m : ℚ) + n) := by nlinarith [sq_nonneg ((m : ℚ) - n)]
  have hmnn : (0 : ℚ) ≤ (m : ℚ) + n := by positivity
  nlinarith

/-! ### Historical computational lower bounds (not formalized)

The theorem above is the *exact* statement proved here.  It should be distinguished from
the purely computational statements found in the literature on betrothed (quasi-amicable)
numbers, such as the assertions that exhaustive searches have found no same-parity
betrothed pair below various explicit search limits.  Those assertions rest on machine
computations over enormous ranges; none of them is formalized in this file, and nothing
below or above depends on them. -/

end Brockian.BetrothedNumbers

