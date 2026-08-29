import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
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

set_option grind.warning false

open MeasureTheory Real FourierTransform Complex

namespace Zeta23Scaffold

/-! ## The tent function -/

/-- The tent (triangle) function, supported on `[-1, 1]`. -/

lemma tent_intm10 (a : ℝ) (ha : a ≠ 0) :
    (∫ x in (-1:ℝ)..0, Complex.exp ((-(a:ℂ) * Complex.I) * x) * ((1:ℂ) + x))
      = Complex.I / (a:ℂ) + 1 / (a:ℂ)^2 - Complex.exp ((a:ℂ) * Complex.I) / (a:ℂ)^2 := by
  have haC : (a:ℂ) ≠ 0 := by exact_mod_cast ha
  have key : ∀ x : ℝ, HasDerivAt
      (fun y : ℝ => Complex.exp ((-(a:ℂ) * Complex.I) * y) *
        (Complex.I * (1 + (y:ℂ)) / (a:ℂ) + 1 / (a:ℂ)^2))
      (Complex.exp ((-(a:ℂ) * Complex.I) * x) * ((1:ℂ) + x)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => ((-(a:ℂ) * Complex.I) * (y:ℂ)))
        (-(a:ℂ) * Complex.I) x := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-(a:ℂ) * Complex.I)
    have h2 := h1.cexp
    have h3 : HasDerivAt (fun y : ℝ => (Complex.I * (1 + (y:ℂ)) / (a:ℂ) + 1 / (a:ℂ)^2))
        (Complex.I / (a:ℂ)) x := by
      have h0 : HasDerivAt (fun y : ℝ => (y:ℂ)) 1 x := by
        simpa using Complex.ofRealCLM.hasDerivAt (x := x)
      have h4 := (h0.const_add (1:ℂ)).mul_const ((a:ℂ)⁻¹)
      simpa [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm] using
        ((h4.const_mul Complex.I).add_const (1 / (a:ℂ)^2))
    have h5 := h2.mul h3
    convert h5 using 1
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => key x)]
  · push_cast
    field_simp
    simp only [mul_zero, neg_zero, Complex.exp_zero]
    ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

