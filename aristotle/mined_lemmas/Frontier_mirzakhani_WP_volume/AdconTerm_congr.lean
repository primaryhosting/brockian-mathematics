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

theorem AdconTerm_congr {V W : ℕ → Multiset ℝ → ℝ} {g : ℕ} {rest : Multiset ℝ}
    (hag : AgreeBelow V W (2 * g + Multiset.card rest + 1)) (t : ℝ) :
    AdconTerm V g rest t = AdconTerm W g rest t := by
  unfold AdconTerm
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
  rw [splitSum_congr hag x y]

/-- The recursion, together with the two base cases, determines the Weil–Petersson volumes
uniquely in the whole stable range (for surfaces with at least one boundary component). -/
