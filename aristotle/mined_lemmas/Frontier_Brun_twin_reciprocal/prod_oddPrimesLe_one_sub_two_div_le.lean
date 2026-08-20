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

lemma prod_oddPrimesLe_one_sub_two_div_le {z : ℕ} (hz : 3 ≤ z) :
    ∏ p ∈ oddPrimesLe z, (1 - 2 / (p : ℝ)) ≤ 4 * Real.exp 1 ^ 2 / (Real.log z) ^ 2 := by
  have hzR : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlog : 1 < Real.log z := by
    have h3 : 1 < Real.log 3 := by
      have hlt : Real.log (Real.exp 1) < Real.log 3 :=
        Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
      rwa [Real.log_exp] at hlt
    have : Real.log 3 ≤ Real.log z := Real.log_le_log (by norm_num) hzR
    linarith
  -- termwise bound
  have hterm : ∏ p ∈ oddPrimesLe z, (1 - 2 / (p : ℝ))
      ≤ ∏ p ∈ oddPrimesLe z, (1 - 1 / (p : ℝ)) ^ 2 := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast oddPrimesLe_three_le hp
      have : 2 / (p : ℝ) ≤ 2 / 3 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3
      linarith
    · have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast oddPrimesLe_three_le hp
      have hppos : (0 : ℝ) < (p : ℝ) := by linarith
      have : (1 - 1 / (p : ℝ)) ^ 2 - (1 - 2 / (p : ℝ)) = (1 / (p : ℝ)) ^ 2 := by
        field_simp
        ring
      nlinarith [sq_nonneg (1 / (p : ℝ))]
  -- relate to the full product over primes
  have h2mem : (2 : ℕ) ∈ Nat.primesBelow (z + 1) := by
    rw [Nat.primesBelow, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.prime_two⟩
  have hsplit : ∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ))
      = (1 - 1 / (2 : ℝ)) * ∏ p ∈ oddPrimesLe z, (1 - 1 / (p : ℝ)) := by
    have h := Finset.mul_prod_erase (Nat.primesBelow (z + 1)) (fun p : ℕ => 1 - 1 / (p : ℝ)) h2mem
    rw [← oddPrimesLe_eq_erase z] at h
    rw [← h]
    norm_num
  have hall := prod_primesBelow_one_sub_inv_le hz
  have hodd : ∏ p ∈ oddPrimesLe z, (1 - 1 / (p : ℝ)) ≤ 2 * (Real.exp 1 / Real.log z) := by
    rw [hsplit] at hall
    norm_num at hall ⊢
    linarith
  have hoddnonneg : 0 ≤ ∏ p ∈ oddPrimesLe z, (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_nonneg (fun p hp => ?_)
    have h3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast oddPrimesLe_three_le hp
    have : 1 / (p : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h3
    linarith
  have hsq : ∏ p ∈ oddPrimesLe z, (1 - 1 / (p : ℝ)) ^ 2
      = (∏ p ∈ oddPrimesLe z, (1 - 1 / (p : ℝ))) ^ 2 := by
    rw [Finset.prod_pow]
  rw [hsq] at hterm
  have hfinal : (∏ p ∈ oddPrimesLe z, (1 - 1 / (p : ℝ))) ^ 2
      ≤ (2 * (Real.exp 1 / Real.log z)) ^ 2 := by
    apply pow_le_pow_left₀ hoddnonneg hodd
  have hexp : (2 * (Real.exp 1 / Real.log z)) ^ 2 = 4 * Real.exp 1 ^ 2 / (Real.log z) ^ 2 := by
    field_simp
    ring
  linarith [hterm, hfinal, hexp.le, hexp.ge]

/-- The tail term of the sieve: `∏_{3 ≤ p ≤ 2^q} (1 + 4/p) ≤ e^20 q^16`. -/
