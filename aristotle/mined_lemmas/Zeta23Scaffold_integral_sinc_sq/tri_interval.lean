import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Complex Filter intervalIntegral
open scoped FourierTransform Topology Real

namespace Zeta23Scaffold

/-- The triangle ("tent") function `x ↦ max 0 (1 - |x|)`, viewed as a complex-valued function. -/

lemma tri_interval (k : ℂ) (hk : k ≠ 0) :
    ∫ x in (-1:ℝ)..1, ((1 - |x| : ℝ) : ℂ) * Complex.exp (k * x)
      = (Complex.exp k + Complex.exp (-k) - 2) / k ^ 2 := by
  have hd1 : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => ((1 - (y:ℂ))/k) * Complex.exp (k*y) + Complex.exp (k*y)/k^2)
      ((1 - (x:ℂ)) * Complex.exp (k*x)) x := by
    intro x
    have h0 : HasDerivAt (fun y : ℝ => (y:ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
    have h1 : HasDerivAt (fun y : ℝ => Complex.exp (k*y)) (Complex.exp (k*x) * (k*1)) x :=
      (h0.const_mul k).cexp
    have h2 := ((((h0.const_sub 1).div_const k).mul h1).add (h1.div_const (k^2)))
    convert h2 using 1
    field_simp
    ring
  have hd2 : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => ((1 + (y:ℂ))/k) * Complex.exp (k*y) - Complex.exp (k*y)/k^2)
      ((1 + (x:ℂ)) * Complex.exp (k*x)) x := by
    intro x
    have h0 : HasDerivAt (fun y : ℝ => (y:ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
    have h1 : HasDerivAt (fun y : ℝ => Complex.exp (k*y)) (Complex.exp (k*x) * (k*1)) x :=
      (h0.const_mul k).cexp
    have h2 := ((((h0.const_add 1).div_const k).mul h1).sub (h1.div_const (k^2)))
    convert h2 using 1
    field_simp
    ring
  have ii1 : IntervalIntegrable (fun x : ℝ => (1 - (x:ℂ)) * Complex.exp (k*x)) volume 0 1 :=
    (by fun_prop : Continuous fun x : ℝ => (1 - (x:ℂ)) * Complex.exp (k*x)).intervalIntegrable 0 1
  have ii2 : IntervalIntegrable (fun x : ℝ => (1 + (x:ℂ)) * Complex.exp (k*x)) volume (-1) 0 :=
    (by fun_prop :
      Continuous fun x : ℝ => (1 + (x:ℂ)) * Complex.exp (k*x)).intervalIntegrable (-1) 0
  have e1 : ∫ x in (0:ℝ)..1, (1 - (x:ℂ)) * Complex.exp (k*x)
      = Complex.exp k/k^2 - 1/k - 1/k^2 := by
    rw [integral_eq_sub_of_hasDerivAt (fun x _ => hd1 x) ii1]
    push_cast
    simp only [mul_zero, Complex.exp_zero, mul_one]
    field_simp
    ring
  have e2 : ∫ x in (-1:ℝ)..0, (1 + (x:ℂ)) * Complex.exp (k*x)
      = 1/k - 1/k^2 + Complex.exp (-k)/k^2 := by
    rw [integral_eq_sub_of_hasDerivAt (fun x _ => hd2 x) ii2]
    push_cast
    simp only [mul_zero, Complex.exp_zero, mul_one]
    field_simp
    ring
  have c1 : (∫ x in (0:ℝ)..1, ((1 - |x| : ℝ):ℂ) * Complex.exp (k*x))
      = ∫ x in (0:ℝ)..1, (1 - (x:ℂ)) * Complex.exp (k*x) := by
    apply integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    simp [abs_of_nonneg hx.1]
  have c2 : (∫ x in (-1:ℝ)..0, ((1 - |x| : ℝ):ℂ) * Complex.exp (k*x))
      = ∫ x in (-1:ℝ)..0, (1 + (x:ℂ)) * Complex.exp (k*x) := by
    apply integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 0)] at hx
    simp [abs_of_nonpos hx.2]
  have hsplit : (∫ x in (-1:ℝ)..1, ((1 - |x| : ℝ):ℂ) * Complex.exp (k*x))
      = (∫ x in (-1:ℝ)..0, ((1 - |x| : ℝ):ℂ) * Complex.exp (k*x))
        + ∫ x in (0:ℝ)..1, ((1 - |x| : ℝ):ℂ) * Complex.exp (k*x) := by
    rw [integral_add_adjacent_intervals]
    · apply Continuous.intervalIntegrable; fun_prop
    · apply Continuous.intervalIntegrable; fun_prop
  rw [hsplit, c1, c2, e1, e2]
  field_simp
  ring

/-- The Fourier transform of the tent function is `(sin (π ξ) / (π ξ))²`. -/
