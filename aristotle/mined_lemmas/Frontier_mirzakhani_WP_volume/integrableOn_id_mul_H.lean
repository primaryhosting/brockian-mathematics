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

theorem integrableOn_id_mul_H (y : ℝ) :
    IntegrableOn (fun x => x * H x y) (Ioi (0:ℝ)) := by
  have h1 := integrableOn_affine_mul_w_shift (0:ℝ) 1 0 y
  have h2 := integrableOn_affine_mul_w_shift (0:ℝ) 1 0 (-y)
  have h3 : IntegrableOn
      (fun u => (1 * u + 0) * w (u + y) + (1 * u + 0) * w (u + -y)) (Ioi (0:ℝ)) :=
    Integrable.add h1 h2
  refine h3.congr_fun ?_ measurableSet_Ioi
  intro x _
  simp only [H, sub_eq_add_neg]
  ring

