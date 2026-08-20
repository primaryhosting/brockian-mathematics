import Mathlib

/-!
# The Fermi–Dirac integral `∫_0^∞ t/(1+e^t) dt = π²/12`

This auxiliary file establishes the elementary integral underlying Mirzakhani's
integration kernel, via the Mellin transform of the Dirichlet eta function.
-/


open Real MeasureTheory Set Complex
open scoped Real

namespace Mirzakhani

/-- Coefficients of the Dirichlet eta series, with the (irrelevant) `n = 0` term set to `0`. -/

theorem integral_Ioi_comp_add_right (f : ℝ → ℝ) (a c : ℝ) :
    (∫ x in Ioi a, f (x + c)) = ∫ u in Ioi (a + c), f u := by
  have h := MeasureTheory.MeasurePreserving.setIntegral_preimage_emb
    (MeasureTheory.measurePreserving_add_right (volume : Measure ℝ) c)
    ((Homeomorph.addRight c).measurableEmbedding) f (Ioi (a + c))
  simpa [Set.preimage_add_const_Ioi] using h

/-- Any affine multiple of a translate of `w` is integrable on a half-line. -/
