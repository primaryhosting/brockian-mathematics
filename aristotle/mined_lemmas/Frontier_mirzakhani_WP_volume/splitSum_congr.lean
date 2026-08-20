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

theorem splitSum_congr {V W : ℕ → Multiset ℝ → ℝ} {g : ℕ} {rest : Multiset ℝ}
    (hag : AgreeBelow V W (2 * g + Multiset.card rest + 1)) (x y : ℝ) :
    splitSum V g rest x y = splitSum W g rest x y := by
  unfold splitSum
  refine Finset.sum_congr rfl (fun g₁ hg₁ => ?_)
  have hg1 : g₁ ≤ g := by have := Finset.mem_range.mp hg₁; omega
  refine congrArg Multiset.sum (Multiset.map_congr rfl (fun I hI => ?_))
  rw [Multiset.mem_powerset] at hI
  have hcI : Multiset.card (rest - I) = Multiset.card rest - Multiset.card I :=
    Multiset.card_sub hI
  have hIle : Multiset.card I ≤ Multiset.card rest := Multiset.card_le_card hI
  split_ifs with hcond
  · obtain ⟨h1, h2⟩ := hcond
    rw [hcI] at h2
    rw [hag g₁ (x ::ₘ I) (by simp [Multiset.card_cons]; omega)
        (by simp [Multiset.card_cons]; omega) (by simp),
      hag (g - g₁) (y ::ₘ (rest - I)) (by simp [Multiset.card_cons, hcI]; omega)
        (by simp [Multiset.card_cons, hcI]; omega) (by simp)]
  · rfl

