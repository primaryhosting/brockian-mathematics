/-
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
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
set_option pp.piBinderTypes true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

namespace Frontier

/-- Cauchy–Schwarz inequality for interval integrals of continuous functions. -/

theorem intervalIntegral_mul_le_sqrt_mul_sqrt {a b : ℝ} (hab : a ≤ b) {u v : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) :
    (∫ t in a..b, u t * v t) ≤
      Real.sqrt (∫ t in a..b, (u t) ^ 2) * Real.sqrt (∫ t in a..b, (v t) ^ 2) := by
  set A : ℝ := ∫ t in a..b, (u t) ^ 2 with hA
  set B : ℝ := ∫ t in a..b, u t * v t with hB
  set C : ℝ := ∫ t in a..b, (v t) ^ 2 with hC
  have hAnonneg : 0 ≤ A := by
    rw [hA]
    exact intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg _)
  have hCnonneg : 0 ≤ C := by
    rw [hC]
    exact intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg _)
  have key : ∀ l : ℝ, 0 ≤ A - 2 * l * B + l ^ 2 * C := by
    intro l
    have hnn : 0 ≤ ∫ t in a..b, (u t - l * v t) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun t _ => sq_nonneg _)
    have hexp : (∫ t in a..b, (u t - l * v t) ^ 2) = A - 2 * l * B + l ^ 2 * C := by
      have e : (fun t => (u t - l * v t) ^ 2)
          = fun t => ((u t) ^ 2 - (2 * l) * (u t * v t)) + (l ^ 2) * ((v t) ^ 2) := by
        funext t; ring
      have i1 : IntervalIntegrable (fun t => (u t) ^ 2) MeasureTheory.volume a b :=
        (hu.pow 2).intervalIntegrable a b
      have i2 : IntervalIntegrable (fun t => u t * v t) MeasureTheory.volume a b :=
        (hu.mul hv).intervalIntegrable a b
      have i3 : IntervalIntegrable (fun t => (v t) ^ 2) MeasureTheory.volume a b :=
        (hv.pow 2).intervalIntegrable a b
      rw [e, intervalIntegral.integral_add (i1.sub (i2.const_mul (2 * l)))
          (i3.const_mul (l ^ 2)), intervalIntegral.integral_sub i1 (i2.const_mul (2 * l)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    linarith [hexp ▸ hnn]
  rcases eq_or_lt_of_le hCnonneg with hC0 | hCpos
  · -- degenerate case: C = 0
    have hB0 : B ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      have := key ((A + 1) / (2 * B))
      rw [← hC0] at this
      have hBne : B ≠ 0 := ne_of_gt hcon
      field_simp at this
      nlinarith [this]
    rw [← hC0]
    simpa using le_trans hB0 (by positivity)
  · have hsq : B ^ 2 ≤ A * C := by
      have := key (B / C)
      have hCne : C ≠ 0 := ne_of_gt hCpos
      field_simp at this
      nlinarith [this]
    have h1 : B ≤ |B| := le_abs_self B
    have h2 : |B| = Real.sqrt (B ^ 2) := (Real.sqrt_sq_eq_abs B).symm
    have h3 : Real.sqrt (B ^ 2) ≤ Real.sqrt (A * C) := Real.sqrt_le_sqrt hsq
    have h4 : Real.sqrt (A * C) = Real.sqrt A * Real.sqrt C := Real.sqrt_mul hAnonneg C
    linarith [h1, h2 ▸ h3, h4 ▸ (le_refl (Real.sqrt (A * C)))]

/-- **Gagliardo–Nirenberg interpolation inequality** (one–dimensional base case,
`L^∞`–`L^2`–`L^2` interpolation).

If `f : ℝ → ℝ` is continuously differentiable with derivative `f'`, and `f` vanishes at the
left endpoint `a` of an interval `[a, b]`, then for every `x ∈ [a, b]`

`|f x|² ≤ 2 ‖f‖_{L²(a,b)} ‖f'‖_{L²(a,b)}`,

i.e. `‖f‖_∞ ≤ √2 ‖f‖_{L²}^{1/2} ‖f'‖_{L²}^{1/2}`, the interpolation exponent being `θ = 1/2`. -/
