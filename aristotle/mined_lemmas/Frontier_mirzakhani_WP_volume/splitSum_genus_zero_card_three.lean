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

theorem splitSum_genus_zero_card_three (V : ℕ → Multiset ℝ → ℝ) (rest : Multiset ℝ)
    (hcard : Multiset.card rest = 3) (x y : ℝ) : splitSum V 0 rest x y = 0 := by
  refine Finset.sum_eq_zero ?_
  intro g₁ hg₁
  have hg : g₁ = 0 := by simpa using Finset.mem_range.mp hg₁
  subst hg
  refine Multiset.sum_eq_zero ?_
  intro z hz
  obtain ⟨I, hI, rfl⟩ := Multiset.mem_map.mp hz
  rw [Multiset.mem_powerset] at hI
  have hc : Multiset.card (rest - I) = 3 - Multiset.card I := by
    rw [Multiset.card_sub hI, hcard]
  have hIle : Multiset.card I ≤ 3 := by
    rw [← hcard]; exact Multiset.card_le_card hI
  rw [if_neg]
  rintro ⟨h1, h2⟩
  rw [hc] at h2
  omega

/-- Evaluation of the `B` term of the recursion in the case `g = 0`, `n = 4`, where all the
volumes occurring are pair-of-pants volumes. -/
