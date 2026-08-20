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

theorem summable_twinCount_div_two_pow :
    Summable (fun m : ℕ => (twinCount (2 ^ m) : ℝ) / 2 ^ m) := by
  obtain ⟨C0, hC0pos, hC0⟩ := poly_div_two_pow_half_le 0
  obtain ⟨C41, hC41pos, hC41⟩ := poly_div_two_pow_half_le 41
  obtain ⟨Cl, hClpos, hCl⟩ := log_sq_le
  have hbound : ∀ m : ℕ, 1024 ≤ m → (twinCount (2 ^ m) : ℝ) / 2 ^ m
      ≤ (2 * C0 + 416000 * Cl + Real.exp 20 * 2 ^ 19 + 21 * C41)
          * (Real.sqrt m / (m : ℝ) ^ 2) := by
    intro m hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by
      have : 0 < m := by omega
      exact_mod_cast this
    have hmR : (1024 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hm1 : (1 : ℝ) ≤ Real.sqrt m := by
      have h1 : (1 : ℝ) ≤ (m : ℝ) := by linarith
      calc (1 : ℝ) = Real.sqrt 1 := by simp
        _ ≤ Real.sqrt m := Real.sqrt_le_sqrt h1
    have key : ∀ c : ℝ, 0 ≤ c → c / (m : ℝ) ^ 2 ≤ c * (Real.sqrt m / (m : ℝ) ^ 2) := by
      intro c hc
      have h1 : c ≤ c * Real.sqrt m := by nlinarith
      calc c / (m : ℝ) ^ 2 ≤ (c * Real.sqrt m) / (m : ℝ) ^ 2 := by gcongr
        _ = c * (Real.sqrt m / (m : ℝ) ^ 2) := by ring
    have hb := twinCount_two_pow_bound hm
    -- term 1
    have h0 := hC0 m (by omega)
    rw [pow_zero] at h0
    have t1 : 2 / (2 : ℝ) ^ (m / 2) ≤ (2 * C0) * (Real.sqrt m / (m : ℝ) ^ 2) := by
      have h2 : 2 / (2 : ℝ) ^ (m / 2) = 2 * (1 / (2 : ℝ) ^ (m / 2)) := by ring
      have h3 : 2 * (1 / (2 : ℝ) ^ (m / 2)) ≤ 2 * (C0 / (m : ℝ) ^ 2) := by linarith
      have h4 : 2 * (C0 / (m : ℝ) ^ 2) = (2 * C0) / (m : ℝ) ^ 2 := by ring
      linarith [key (2 * C0) (by positivity)]
    -- term 2
    have hL := hCl m (by omega)
    have t2 : 416000 * ((Nat.log 2 m : ℝ)) ^ 2 / (m : ℝ) ^ 2
        ≤ (416000 * Cl) * (Real.sqrt m / (m : ℝ) ^ 2) := by
      have hnum : 416000 * ((Nat.log 2 m : ℝ)) ^ 2 ≤ 416000 * (Cl * Real.sqrt m) := by linarith
      calc 416000 * ((Nat.log 2 m : ℝ)) ^ 2 / (m : ℝ) ^ 2
          ≤ (416000 * (Cl * Real.sqrt m)) / (m : ℝ) ^ 2 := by gcongr
        _ = (416000 * Cl) * (Real.sqrt m / (m : ℝ) ^ 2) := by ring
    -- term 3
    have t3 : Real.exp 20 * 2 ^ 19 / (m : ℝ) ^ 4
        ≤ (Real.exp 20 * 2 ^ 19) * (Real.sqrt m / (m : ℝ) ^ 2) := by
      have hp24 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
      have hp4 : (0 : ℝ) < (m : ℝ) ^ 4 := by positivity
      have hcmp : (1 : ℝ) / (m : ℝ) ^ 4 ≤ Real.sqrt m / (m : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ hp4 (by positivity)]
        nlinarith
      have hE : Real.exp 20 * 2 ^ 19 / (m : ℝ) ^ 4
          = (Real.exp 20 * 2 ^ 19) * (1 / (m : ℝ) ^ 4) := by ring
      have hpos : (0 : ℝ) ≤ Real.exp 20 * 2 ^ 19 := by positivity
      rw [hE]
      exact mul_le_mul_of_nonneg_left hcmp hpos
    -- term 4
    have h41 := hC41 m (by omega)
    have t4 : 21 * (m : ℝ) ^ 41 / (2 : ℝ) ^ (m / 2) ≤ (21 * C41) * (Real.sqrt m / (m : ℝ) ^ 2) := by
      have h2 : 21 * (m : ℝ) ^ 41 / (2 : ℝ) ^ (m / 2) = 21 * ((m : ℝ) ^ 41 / (2 : ℝ) ^ (m / 2)) := by
        ring
      have h3 : 21 * ((m : ℝ) ^ 41 / (2 : ℝ) ^ (m / 2)) ≤ 21 * (C41 / (m : ℝ) ^ 2) := by linarith
      have h4 : 21 * (C41 / (m : ℝ) ^ 2) = (21 * C41) / (m : ℝ) ^ 2 := by ring
      linarith [key (21 * C41) (by positivity)]
    nlinarith [t1, t2, t3, t4, hb]
  have hS : Summable (fun m : ℕ => (2 * C0 + 416000 * Cl + Real.exp 20 * 2 ^ 19 + 21 * C41)
      * (Real.sqrt m / (m : ℝ) ^ 2)) :=
    summable_sqrt_div_sq.mul_left _
  have hS' : Summable (fun n : ℕ => (2 * C0 + 416000 * Cl + Real.exp 20 * 2 ^ 19 + 21 * C41)
      * (Real.sqrt ((n + 1024 : ℕ)) / ((n + 1024 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1024).mpr hS
  rw [← summable_nat_add_iff 1024]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hS'
  exact hbound (n + 1024) (by omega)

end Brun

import Mathlib

/-!
# Bonferroni inequalities

Truncated inclusion-exclusion: for an even truncation level `k`, the alternating partial sum
of binomial coefficients is an upper bound for the indicator of "no condition holds".
-/

namespace Brun

open Finset

/-- The alternating partial sum of binomial coefficients. -/
