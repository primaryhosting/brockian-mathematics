import Mathlib

/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Set Filter Real
open scoped Topology ENNReal

namespace Zeta23Scaffold

/-- The auxiliary kernel `t * sin x ^ 2 * exp (-(t * x))`, used to compute the integral of
`(sin x / x) ^ 2` by Tonelli's theorem, via `1 / x ^ 2 = ∫ t in (0, ∞), t * exp (-(t * x))`. -/

lemma hasDerivAt_sinSqExpPrim (t x : ℝ) :
    HasDerivAt (sinSqExpPrim t) (sincKer x t) x := by
  have hl : HasDerivAt (fun x : ℝ => -(t * x)) (-t) x := by
    simpa using ((hasDerivAt_id x).const_mul t).neg
  have he : HasDerivAt (fun x : ℝ => Real.exp (-(t * x))) (Real.exp (-(t * x)) * (-t)) x := hl.exp
  have h2x : HasDerivAt (fun x : ℝ => 2 * x) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  have hc : HasDerivAt (fun x : ℝ => Real.cos (2 * x)) (-Real.sin (2 * x) * 2) x := h2x.cos
  have hs : HasDerivAt (fun x : ℝ => Real.sin (2 * x)) (Real.cos (2 * x) * 2) x := h2x.sin
  have hA : HasDerivAt
      (fun x : ℝ => -1 / 2 - t * (-t * Real.cos (2 * x) + 2 * Real.sin (2 * x)) / (2 * (t ^ 2 + 4)))
      (-(t * (-t * (-Real.sin (2 * x) * 2) + 2 * (Real.cos (2 * x) * 2)) / (2 * (t ^ 2 + 4)))) x := by
    have h := (((hc.const_mul (-t)).add (hs.const_mul 2)).const_mul t).div_const (2 * (t ^ 2 + 4))
    exact (h.const_sub (-1 / 2 : ℝ)).congr_deriv (by ring)
  refine (he.mul hA).congr_deriv ?_
  have h4 : (2 : ℝ) * (t ^ 2 + 4) ≠ 0 := by positivity
  have hsin : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := Real.sin_two_mul x
  have hcos : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
    rw [Real.cos_two_mul']; nlinarith [Real.sin_sq_add_cos_sq x]
  simp only [sincKer, hsin, hcos]
  field_simp
  ring

