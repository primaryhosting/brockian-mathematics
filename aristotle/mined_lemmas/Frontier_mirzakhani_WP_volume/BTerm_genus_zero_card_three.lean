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

theorem BTerm_genus_zero_card_three {V : ℕ → Multiset ℝ → ℝ}
    (hV3 : ∀ s : Multiset ℝ, Multiset.card s = 3 → V 0 s = 1)
    (rest : Multiset ℝ) (hcard : Multiset.card rest = 3) (t : ℝ) :
    BTerm V 0 rest t = (1 / 2) * (rest.map fun Lj => t ^ 2 + Lj ^ 2 + 4 * π ^ 2 / 3).sum := by
  unfold BTerm
  congr 2
  refine Multiset.map_congr rfl ?_
  intro Lj hLj
  have hV : ∀ x : ℝ, V 0 (x ::ₘ rest.erase Lj) = 1 := by
    intro x
    refine hV3 _ ?_
    simp [Multiset.card_cons, Multiset.card_erase_of_mem hLj, hcard]
  calc (∫ x in Ioi (0:ℝ), x * (Mirzakhani.H x (t + Lj) + Mirzakhani.H x (t - Lj))
        * V 0 (x ::ₘ rest.erase Lj))
      = ∫ x in Ioi (0:ℝ), x * (Mirzakhani.H x (t + Lj) + Mirzakhani.H x (t - Lj)) :=
        setIntegral_congr_fun measurableSet_Ioi (fun x _ => by rw [hV x]; ring)
    _ = (t + Lj) ^ 2 / 2 + (t - Lj) ^ 2 / 2 + 4 * π ^ 2 / 3 :=
        Mirzakhani.integral_id_mul_H_pair _ _
    _ = t ^ 2 + Lj ^ 2 + 4 * π ^ 2 / 3 := by ring

/-- The four-holed sphere volume, computed from the recursion: `V_{0,4} = 2π² + ½ Σ Lᵢ²`. -/
