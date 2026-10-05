/-
# Unruh Effect
Category: Frontier Phys
Target: Phys.unruh_effect
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the mandated
-- header above is written as an ordinary block comment; its text is unchanged.)

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

namespace Phys

/-! ## Definitions -/

/-- The **Unruh temperature** `T = ℏ a / (2 π c k_B)` associated with proper acceleration `a`. -/

theorem rindlerIntervalSqC_kms_period_minimal (a c : ℝ) (ha : 0 < a) (hc : 0 < c) (b : ℝ)
    (hb : 0 < b)
    (hper : ∀ Δ : ℂ, rindlerIntervalSqC a c (Δ + Complex.I * (b : ℂ))
      = rindlerIntervalSqC a c Δ) :
    2 * Real.pi * c / a ≤ b := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have h0 := hper 0
  simp only [rindlerIntervalSqC, zero_add, mul_zero, zero_div, Complex.sinh_zero] at h0
  have hcoef : (4 : ℂ) * ((c : ℂ) ^ 2 / (a : ℂ)) ^ 2 ≠ 0 := by
    have hne : ((c : ℂ) ^ 2 / (a : ℂ)) ≠ 0 := div_ne_zero (pow_ne_zero 2 hc') ha'
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hne)
  have hs : Complex.sinh ((a : ℂ) * (Complex.I * (b : ℂ)) / (2 * (c : ℂ))) ^ 2 = 0 := by
    have h0' := h0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h0'
    exact (mul_eq_zero.mp h0').resolve_left hcoef
  have hs0 : Complex.sinh ((a : ℂ) * (Complex.I * (b : ℂ)) / (2 * (c : ℂ))) = 0 :=
    pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hs
  have harg : (a : ℂ) * (Complex.I * (b : ℂ)) / (2 * (c : ℂ))
      = ((a * b / (2 * c) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [harg, Complex.sinh_mul_I] at hs0
  have hsin : Real.sin (a * b / (2 * c)) = 0 := by
    have hcs : Complex.sin (((a * b / (2 * c) : ℝ) : ℂ)) = 0 := by
      rcases mul_eq_zero.mp hs0 with h | h
      · exact h
      · exact absurd h Complex.I_ne_zero
    rw [← Complex.ofReal_sin] at hcs
    exact_mod_cast hcs
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
  have hpos : 0 < a * b / (2 * c) := by positivity
  have hn1 : (1 : ℤ) ≤ n := by
    by_contra hcon
    push_neg at hcon
    have hle : (n : ℝ) ≤ 0 := by exact_mod_cast Int.lt_add_one_iff.mp hcon
    nlinarith [Real.pi_pos]
  have hpi_le : Real.pi ≤ a * b / (2 * c) := by
    rw [← hn]
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    nlinarith [Real.pi_pos]
  have hcc : (0 : ℝ) < 2 * c := by linarith
  rw [le_div_iff₀ hcc] at hpi_le
  rw [div_le_iff₀ ha]
  linarith

/-! ## Thermality: the inverse temperature is `ℏ/(k_B T_U)` -/

/-- The KMS imaginary period `2πc/a` equals `ℏ / (k_B T)` exactly for `T` the Unruh
temperature. -/
