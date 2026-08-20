import Mathlib
/-!
# Integral Sinc Sq
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_sq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Real Complex
open scoped FourierTransform

noncomputable section

namespace Zeta23Scaffold

/-- The tent function `t ↦ max (1 - |t|) 0`. -/

lemma real_tent_cos (a : ℝ) (ha : a ≠ 0) :
    ∫ v in (0 : ℝ)..1, (1 - v) * Real.cos (a * v) = (1 - Real.cos a) / a ^ 2 := by
  have key : ∀ v ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => (1 - t) * Real.sin (a * t) / a - Real.cos (a * t) / a ^ 2)
        ((1 - v) * Real.cos (a * v)) v := by
    intro v _
    have h1 : HasDerivAt (fun t : ℝ => a * t) a v := by
      simpa using (hasDerivAt_id v).const_mul a
    have hs : HasDerivAt (fun t : ℝ => Real.sin (a * t)) (Real.cos (a * v) * a) v :=
      (Real.hasDerivAt_sin (a * v)).comp v h1
    have hc : HasDerivAt (fun t : ℝ => Real.cos (a * t)) (-Real.sin (a * v) * a) v :=
      (Real.hasDerivAt_cos (a * v)).comp v h1
    have hlin : HasDerivAt (fun t : ℝ => 1 - t) (-1) v := by
      simpa using (hasDerivAt_id v).const_sub 1
    have h := ((hlin.mul hs).div_const a).sub (hc.div_const (a ^ 2))
    convert h using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key]
  · simp
    field_simp
    ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The Fourier transform of the tent function is `sinc (π ξ) ^ 2`. -/
