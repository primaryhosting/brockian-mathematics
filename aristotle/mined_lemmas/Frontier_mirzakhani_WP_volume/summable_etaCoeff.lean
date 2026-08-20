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

theorem summable_etaCoeff : Summable (fun n : ℕ => ‖etaCoeff n‖ / (n : ℝ) ^ ((2 : ℂ).re)) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℝ)) := by
    rw [Real.summable_one_div_nat_rpow]; norm_num
  refine h.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  simp only [Complex.re_ofNat]
  gcongr
  simp only [etaCoeff]
  split_ifs with h0
  · simp
  · simp [norm_pow]

/-- **The Fermi–Dirac integral**: `∫_0^∞ t/(1+e^t) dt = π²/12`. -/
