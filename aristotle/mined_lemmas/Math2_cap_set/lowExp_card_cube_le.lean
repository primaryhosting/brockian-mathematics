import RequestProject.CapExpand

/-!
# The Ellenberg–Gijswijt bound

Combining the slice-rank bound with the polynomial expansion gives
`|A| ≤ 3 · #{exponent vectors of degree ≤ 2n/3}` for every 3AP-free `A ⊆ 𝔽₃ⁿ`.
-/

open scoped BigOperators
open Finset

namespace CapSetAux

/-- In `𝔽₃ⁿ`, a 3AP-free set contains no nontrivial triple summing to zero. -/

lemma lowExp_card_cube_le (n : ℕ) : ((lowExp n).card : ℝ) ^ 3 ≤ (343 / 16) ^ n := by
  have hmul := lowExp_card_mul_le n
  have hcard : ((lowExp n).card : ℝ) ≤ (7 / 4) ^ n * 2 ^ (D0 n) := by
    have h2 : (0 : ℝ) < 2 ^ (D0 n) := by positivity
    have : ((lowExp n).card : ℝ) * ((1 : ℝ) / 2) ^ (D0 n) * 2 ^ (D0 n)
        ≤ (7 / 4) ^ n * 2 ^ (D0 n) := by
      exact mul_le_mul_of_nonneg_right hmul (le_of_lt h2)
    calc ((lowExp n).card : ℝ)
        = ((lowExp n).card : ℝ) * ((1 : ℝ) / 2) ^ (D0 n) * 2 ^ (D0 n) := by
          rw [mul_assoc, ← mul_pow]
          norm_num
      _ ≤ (7 / 4) ^ n * 2 ^ (D0 n) := this
  have hnn : (0 : ℝ) ≤ ((lowExp n).card : ℝ) := by positivity
  have hcube : ((lowExp n).card : ℝ) ^ 3 ≤ ((7 / 4) ^ n * 2 ^ (D0 n)) ^ 3 :=
    pow_le_pow_left₀ hnn hcard 3
  have hD : 3 * D0 n ≤ 2 * n := by
    unfold D0
    omega
  have hexp : ((7 / 4 : ℝ) ^ n * 2 ^ (D0 n)) ^ 3 ≤ (343 / 16) ^ n := by
    have h1 : ((7 / 4 : ℝ) ^ n * 2 ^ (D0 n)) ^ 3 = (343 / 64 : ℝ) ^ n * 2 ^ (3 * D0 n) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm n 3, mul_comm (D0 n) 3, pow_mul]
      norm_num
    have h2 : (2 : ℝ) ^ (3 * D0 n) ≤ 2 ^ (2 * n) :=
      pow_le_pow_right₀ (by norm_num) hD
    have h3 : (0 : ℝ) < (343 / 64 : ℝ) ^ n := by positivity
    calc ((7 / 4 : ℝ) ^ n * 2 ^ (D0 n)) ^ 3 = (343 / 64 : ℝ) ^ n * 2 ^ (3 * D0 n) := h1
      _ ≤ (343 / 64 : ℝ) ^ n * 2 ^ (2 * n) := by
          exact mul_le_mul_of_nonneg_left h2 (le_of_lt h3)
      _ = (343 / 16 : ℝ) ^ n := by
          have h4 : (2 : ℝ) ^ (2 * n) = 4 ^ n := by
            rw [pow_mul]; norm_num
          rw [h4, ← mul_pow]
          norm_num
  linarith

end CapSetAux

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

