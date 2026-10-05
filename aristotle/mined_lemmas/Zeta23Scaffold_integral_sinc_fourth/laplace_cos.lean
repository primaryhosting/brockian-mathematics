/-
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Zeta23Scaffold

open MeasureTheory Set Real Filter Topology

/-! ### Laplace transform of `cos (a * x)` on `(0, ∞)` -/

/-- The function `x ↦ e^{-t x} cos (a x)` is integrable on `(0, ∞)` when `t > 0`. -/

theorem laplace_cos (t a : ℝ) (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), Real.exp (-(t * x)) * Real.cos (a * x) = t / (t ^ 2 + a ^ 2) := by
  have hden : (0 : ℝ) < t ^ 2 + a ^ 2 := by positivity
  set F : ℝ → ℝ := fun x =>
    Real.exp (-(t * x)) * (-t * Real.cos (a * x) + a * Real.sin (a * x)) / (t ^ 2 + a ^ 2) with hF
  have hderiv : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt F (Real.exp (-(t * x)) * Real.cos (a * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-(t * x))) (-t * Real.exp (-(t * x))) x := by
      have : HasDerivAt (fun x : ℝ => -(t * x)) (-t) x := by
        simpa using ((hasDerivAt_id x).const_mul t).neg
      simpa [mul_comm] using this.exp
    have h2 : HasDerivAt (fun x : ℝ => Real.cos (a * x)) (-(a * Real.sin (a * x))) x := by
      have : HasDerivAt (fun x : ℝ => a * x) a x := by simpa using (hasDerivAt_id x).const_mul a
      simpa [mul_comm] using this.cos
    have h3 : HasDerivAt (fun x : ℝ => Real.sin (a * x)) (a * Real.cos (a * x)) x := by
      have : HasDerivAt (fun x : ℝ => a * x) a x := by simpa using (hasDerivAt_id x).const_mul a
      simpa [mul_comm] using this.sin
    have h5 := ((h1.mul ((h2.const_mul (-t)).add (h3.const_mul a))).div_const (t ^ 2 + a ^ 2))
    convert h5 using 1
    simp only [Pi.add_apply]
    field_simp
    ring
  have htend : Tendsto F atTop (𝓝 0) := by
    have hb : Tendsto (fun x : ℝ => (t + |a|) / (t ^ 2 + a ^ 2) * Real.exp (-(t * x)))
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun x : ℝ => Real.exp (-(t * x))) atTop (𝓝 0) := by
        apply Real.tendsto_exp_atBot.comp
        exact Filter.tendsto_neg_atBot_iff.2 (Filter.Tendsto.const_mul_atTop ht tendsto_id)
      simpa using h0.const_mul ((t + |a|) / (t ^ 2 + a ^ 2))
    refine squeeze_zero_norm (fun x => ?_) hb
    have hN : |(-t * Real.cos (a * x) + a * Real.sin (a * x))| ≤ t + |a| := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos ht]
      have h1 := Real.abs_cos_le_one (a * x)
      have h3 : |a| * |Real.sin (a * x)| ≤ |a| * 1 := by
        gcongr
        exact Real.abs_sin_le_one _
      nlinarith [abs_nonneg a, abs_nonneg (Real.cos (a * x))]
    rw [hF]
    simp only
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hden, abs_of_pos (Real.exp_pos _)]
    rw [div_le_iff₀ hden]
    calc Real.exp (-(t * x)) * |(-t * Real.cos (a * x) + a * Real.sin (a * x))|
        ≤ Real.exp (-(t * x)) * (t + |a|) := by gcongr
      _ = (t + |a|) / (t ^ 2 + a ^ 2) * Real.exp (-(t * x)) * (t ^ 2 + a ^ 2) := by field_simp
  have hres := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv
    (laplace_cos_integrableOn t a ht) htend
  rw [hres, hF]
  simp
  field_simp

/-- The Laplace transform of `sin⁴`: an explicit rational function of `t`. -/
