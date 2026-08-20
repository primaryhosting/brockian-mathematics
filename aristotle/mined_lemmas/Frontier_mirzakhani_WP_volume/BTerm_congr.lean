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

theorem BTerm_congr {V W : ℕ → Multiset ℝ → ℝ} {g : ℕ} {rest : Multiset ℝ}
    (hag : AgreeBelow V W (2 * g + Multiset.card rest + 1))
    (hM : 4 ≤ 2 * g + Multiset.card rest + 1) (t : ℝ) :
    BTerm V g rest t = BTerm W g rest t := by
  unfold BTerm
  congr 2
  refine Multiset.map_congr rfl (fun Lj hLj => ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  have hc : Multiset.card (rest.erase Lj) = Multiset.card rest - 1 :=
    Multiset.card_erase_of_mem hLj
  have hpos : 0 < Multiset.card rest := Multiset.card_pos.mpr (fun hz => by simp [hz] at hLj)
  rw [hag g (x ::ₘ rest.erase Lj) (by simp [Multiset.card_cons, hc]; omega)
    (by simp [Multiset.card_cons, hc]; omega) (by simp)]

