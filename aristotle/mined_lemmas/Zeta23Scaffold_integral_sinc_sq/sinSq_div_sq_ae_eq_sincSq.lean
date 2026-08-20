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

lemma sinSq_div_sq_ae_eq_sincSq :
    (fun x : ℝ => (Real.sin x / x) ^ 2) =ᵐ[volume] fun x : ℝ => (Real.sinc x) ^ 2 := by
  have h0 : ({(0:ℝ)}ᶜ : Set ℝ) ∈ ae (volume : Measure ℝ) := by
    simp [MeasureTheory.compl_mem_ae_iff]
  filter_upwards [h0] with x hx
  rw [Real.sinc_of_ne_zero hx]

/-- `(sin x / x)²` is integrable on `ℝ`. -/
