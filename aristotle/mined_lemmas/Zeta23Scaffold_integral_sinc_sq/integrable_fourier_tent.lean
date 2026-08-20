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

lemma integrable_fourier_tent : Integrable (𝓕 tent) := by
  have h : Integrable (fun ξ : ℝ => ((Real.sinc (π * ξ) ^ 2 : ℝ) : ℂ)) :=
    Integrable.ofReal (integrable_sinc_sq.comp_mul_left' Real.pi_ne_zero)
  exact h.congr (Filter.Eventually.of_forall fun ξ => (fourier_tent ξ).symm)

