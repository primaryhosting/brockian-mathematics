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

lemma prod_primesBelow_one_sub_inv_le {z : ℕ} (hz : 3 ≤ z) :
    ∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ)) ≤ Real.exp 1 / Real.log z := by
  have hzR : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hlogpos : 1 < Real.log z := by
    have : Real.log 3 ≤ Real.log z := Real.log_le_log (by norm_num) hzR
    have h3 : 1 < Real.log 3 := by
      have hlt : Real.log (Real.exp 1) < Real.log 3 :=
        Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
      rwa [Real.log_exp] at hlt
    linarith
  set s : ℝ := 1 + 1 / Real.log z with hs_def
  have hs1 : 1 < s := by
    rw [hs_def]
    have : 0 < 1 / Real.log z := by positivity
    linarith
  -- lower bound for the partial sum
  have hlow : Real.exp (-1) * ∑ n ∈ Icc 1 z, (1 / (n : ℝ)) ≤ ∑ n ∈ Icc 1 z, (n : ℝ) ^ (-s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun n hn => ?_)
    simp only [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hlognz : Real.log n ≤ Real.log z := by
      apply Real.log_le_log hnpos
      exact_mod_cast hn.2
    rw [Real.rpow_def_of_pos hnpos]
    have h1 : (1 : ℝ) / (n : ℝ) = Real.exp (-Real.log n) := by
      rw [Real.exp_neg, Real.exp_log hnpos]
      simp
    rw [h1, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : Real.log n * (1 / Real.log z) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]
      exact hlognz
    rw [hs_def]
    nlinarith
  -- upper bound for the Euler factors
  have hup : ∏ p ∈ Nat.primesBelow (z + 1), (1 - (p : ℝ) ^ (-s))⁻¹
      ≤ ∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ))⁻¹ := by
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
      have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      have : (p : ℝ) ^ (-s) ≤ 1 := by
        apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
        linarith
      have hlt : (p : ℝ) ^ (-s) < 1 := by
        have : (p : ℝ) ^ (-s) < (p : ℝ) ^ (0 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt (by linarith)
          linarith
        simpa using this
      have : 0 < 1 - (p : ℝ) ^ (-s) := by linarith
      positivity
    · have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
      have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
      have hppos : (0 : ℝ) < (p : ℝ) := by linarith
      have hle : (p : ℝ) ^ (-s) ≤ (p : ℝ) ^ (-1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by linarith)
        linarith
      have hinv : (p : ℝ) ^ (-1 : ℝ) = 1 / (p : ℝ) := by
        rw [Real.rpow_neg_one]; simp
      rw [hinv] at hle
      have h1 : 0 < 1 - 1 / (p : ℝ) := by
        have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hpR
        linarith
      exact inv_anti₀ h1 (by linarith)
  -- harmonic sum lower bound
  have hharm : Real.log z ≤ ∑ n ∈ Icc 1 z, (1 / (n : ℝ)) := by
    have h1 : Real.log ((z : ℝ)) ≤ Real.log ((z : ℕ) + 1 : ℕ) := by
      apply Real.log_le_log (by linarith)
      push_cast
      linarith
    have h2 := log_add_one_le_harmonic z
    have h3 : ((harmonic z : ℚ) : ℝ) = ∑ n ∈ Icc 1 z, (1 / (n : ℝ)) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp [one_div]
    rw [h3] at h2
    exact le_trans h1 h2
  have hkey := sum_rpow_le_prod_primesBelow z hs1
  have hprodpos : 0 < ∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_pos (fun p hp => ?_)
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primesBelow hp).two_le
    have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hpR
    linarith
  have hinvprod : ∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ))⁻¹
      = (∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ)))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
  rw [hinvprod] at hup
  -- combine
  have hchain : Real.exp (-1) * Real.log z
      ≤ (∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ)))⁻¹ := by
    calc Real.exp (-1) * Real.log z
        ≤ Real.exp (-1) * ∑ n ∈ Icc 1 z, (1 / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hharm (le_of_lt (Real.exp_pos _))
      _ ≤ ∑ n ∈ Icc 1 z, (n : ℝ) ^ (-s) := hlow
      _ ≤ _ := le_trans hkey hup
  rw [le_inv_comm₀ (by positivity) hprodpos] at hchain
  calc ∏ p ∈ Nat.primesBelow (z + 1), (1 - 1 / (p : ℝ))
      ≤ (Real.exp (-1) * Real.log z)⁻¹ := hchain
    _ = Real.exp 1 / Real.log z := by
        rw [Real.exp_neg]
        field_simp

/-! ### Mertens-type upper bound via the primorial -/

/-- The number of primes in `(2^j, 2^(j+1)]` is at most `2^(j+2)/j`. -/
