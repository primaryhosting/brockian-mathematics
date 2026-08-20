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

theorem integral_id_mul_H_pair (p q : ℝ) :
    (∫ x in Ioi (0:ℝ), x * (H x p + H x q)) = p ^ 2 / 2 + q ^ 2 / 2 + 4 * π ^ 2 / 3 := by
  have h1 := integrableOn_id_mul_H p
  have h2 := integrableOn_id_mul_H q
  have hsum : (∫ x in Ioi (0:ℝ), x * (H x p + H x q))
      = (∫ x in Ioi (0:ℝ), x * H x p) + ∫ x in Ioi (0:ℝ), x * H x q := by
    rw [← integral_add h1 h2]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring)
  rw [hsum, integral_id_mul_H, integral_id_mul_H]
  ring

end Mirzakhani

