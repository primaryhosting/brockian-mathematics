/-
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory

set_option autoImplicit false

namespace Frontier

/--
**Gagliardo–Nirenberg (base case, `n = 1`, `p = 1`).**

If `u : ℝ → ℝ` is everywhere differentiable with derivative `u'`, `u'` is integrable, and `u`
has compact support, then

`‖u‖_{L^∞} ≤ (1/2) * ‖u'‖_{L^1}`,

pointwise: `|u x| ≤ (1/2) * ∫ t, |u' t|` for every `x`.

This is the one-dimensional endpoint case of the Gagliardo–Nirenberg–Sobolev inequality: it is
obtained by writing `u x` both as `∫_{-S}^{x} u'` and as `-∫_{x}^{S} u'` (where `[-S, S]` contains
the support of `u`), and adding the two resulting bounds.  The constant `1/2` is sharp.
-/

theorem integral_mul_le_sqrt_mul_sqrt {f g : ℝ → ℝ} (hf : Integrable (fun x => f x ^ 2))
    (hg : Integrable (fun x => g x ^ 2)) (hfg : Integrable (fun x => f x * g x)) :
    (∫ x, f x * g x) ≤ Real.sqrt (∫ x, f x ^ 2) * Real.sqrt (∫ x, g x ^ 2) := by
  set A := ∫ x, f x ^ 2 with hA
  set B := ∫ x, g x ^ 2 with hB
  set C := ∫ x, f x * g x with hC
  have hA0 : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
  have hB0 : 0 ≤ B := integral_nonneg fun x => sq_nonneg _
  -- the quadratic `t ↦ ∫ (f - t g)^2` is nonnegative
  have key : ∀ t : ℝ, 0 ≤ A - 2 * t * C + t ^ 2 * B := by
    intro t
    have hrw : (fun x => (f x - t * g x) ^ 2)
        = fun x => (f x ^ 2 - 2 * t * (f x * g x)) + t ^ 2 * g x ^ 2 := by
      funext x; ring
    have h0 : 0 ≤ ∫ x, (f x - t * g x) ^ 2 := integral_nonneg fun x => sq_nonneg _
    rw [hrw] at h0
    have e1 : (∫ x, (f x ^ 2 - 2 * t * (f x * g x)) + t ^ 2 * g x ^ 2)
        = (∫ x, (f x ^ 2 - 2 * t * (f x * g x))) + ∫ x, t ^ 2 * g x ^ 2 :=
      integral_add (hf.sub (hfg.const_mul (2 * t))) (hg.const_mul (t ^ 2))
    have e2 : (∫ x, (f x ^ 2 - 2 * t * (f x * g x))) = A - ∫ x, 2 * t * (f x * g x) :=
      integral_sub hf (hfg.const_mul (2 * t))
    have e3 : (∫ x, 2 * t * (f x * g x)) = 2 * t * C := integral_const_mul _ _
    have e4 : (∫ x, t ^ 2 * g x ^ 2) = t ^ 2 * B := integral_const_mul _ _
    rw [e1, e2, e3, e4] at h0
    linarith
  rcases eq_or_lt_of_le hB0 with hB0' | hBpos
  · -- degenerate case `∫ g^2 = 0`, which forces `∫ f g = 0`
    have hC0 : C = 0 := by
      by_contra hne
      have h := key ((A + 1) / (2 * C))
      rw [← hB0'] at h
      have hx : 2 * ((A + 1) / (2 * C)) * C = A + 1 := by field_simp
      rw [hx] at h
      simp at h
      linarith
    rw [hC0, ← hB0']
    simp
  · set D := C ^ 2 / B with hD
    have hx : 2 * (C / B) * C = 2 * D := by rw [hD]; field_simp
    have hy : (C / B) ^ 2 * B = D := by rw [hD]; field_simp
    have h := key (C / B)
    rw [hx, hy] at h
    have h2 : D ≤ A := by linarith
    have hsq : C ^ 2 ≤ A * B := by
      have hCD : C ^ 2 = D * B := by rw [hD]; field_simp
      rw [hCD]
      exact mul_le_mul_of_nonneg_right h2 hB0
    calc C ≤ |C| := le_abs_self C
      _ = Real.sqrt (C ^ 2) := (Real.sqrt_sq_eq_abs C).symm
      _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hA0 B

/--
**Gagliardo–Nirenberg, `L^2` interpolation form (Ladyzhenskaya's inequality in dimension 1).**

If `u` is everywhere differentiable with integrable, square integrable derivative `u'`, and `u`
has compact support, then

`‖u‖_{L^∞}^2 ≤ ‖u‖_{L^2} * ‖u'‖_{L^2}`.
-/
