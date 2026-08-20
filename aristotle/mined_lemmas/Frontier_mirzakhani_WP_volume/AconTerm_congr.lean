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

theorem AconTerm_congr {V W : ℕ → Multiset ℝ → ℝ} {g : ℕ} {rest : Multiset ℝ}
    (hag : AgreeBelow V W (2 * g + Multiset.card rest + 1))
    (hM : 4 ≤ 2 * g + Multiset.card rest + 1) (t : ℝ) :
    AconTerm V g rest t = AconTerm W g rest t := by
  unfold AconTerm
  split_ifs with hg
  · congr 1
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    refine setIntegral_congr_fun measurableSet_Ioi (fun y _ => ?_)
    rw [hag (g - 1) (x ::ₘ y ::ₘ rest) (by simp [Multiset.card_cons]; omega)
      (by simp [Multiset.card_cons]; omega) (by simp)]
  · rfl

