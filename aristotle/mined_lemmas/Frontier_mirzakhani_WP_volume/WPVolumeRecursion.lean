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

theorem WPVolumeRecursion.unique {V W : ℕ → Multiset ℝ → ℝ} (hV : WPVolumeRecursion V)
    (hW : WPVolumeRecursion W) (g : ℕ) (s : Multiset ℝ) (hs : 3 ≤ 2 * g + Multiset.card s)
    (hne : s ≠ 0) : V g s = W g s := by
  suffices H : ∀ m : ℕ, ∀ (g : ℕ) (s : Multiset ℝ), 2 * g + Multiset.card s = m → 3 ≤ m →
      s ≠ 0 → V g s = W g s from H _ g s rfl hs hne
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro g s hm h3 hne
    rcases eq_or_lt_of_le h3 with h3eq | h3lt
    · have hcases : (g = 0 ∧ Multiset.card s = 3) ∨ (g = 1 ∧ Multiset.card s = 1) := by omega
      rcases hcases with ⟨rfl, hc⟩ | ⟨rfl, hc⟩
      · rw [hV.volume_card_three hc, hW.volume_card_three hc]
      · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hc
        rw [hV.one_holed_torus, hW.one_holed_torus]
    · obtain ⟨L0, hL0⟩ := Multiset.exists_mem_of_ne_zero hne
      obtain ⟨rest, rfl⟩ := Multiset.exists_cons_of_mem hL0
      have hcard : 2 * g + Multiset.card rest + 1 = m := by
        rw [Multiset.card_cons] at hm; omega
      have hM : 4 ≤ 2 * g + Multiset.card rest + 1 := by omega
      have hag : AgreeBelow V W (2 * g + Multiset.card rest + 1) := by
        intro g' s' hlt h3' hne'
        exact ih (2 * g' + Multiset.card s') (by omega) g' s' rfl h3' hne'
      have hall : ∀ L : ℝ, L ≠ 0 → V g (L ::ₘ rest) = W g (L ::ₘ rest) := by
        intro L hL
        have e1 := hV.recursion g rest L (by omega)
        have e2 := hW.recursion g rest L (by omega)
        have hint : ∀ t ∈ Set.uIcc (0:ℝ) L,
            AconTerm V g rest t + AdconTerm V g rest t + BTerm V g rest t
              = AconTerm W g rest t + AdconTerm W g rest t + BTerm W g rest t := by
          intro t _
          rw [AconTerm_congr hag hM t, BTerm_congr hag hM t, AdconTerm_congr hag t]
        rw [intervalIntegral.integral_congr hint] at e1
        exact mul_left_cancel₀ hL (e1.trans e2.symm)
      have heq := Continuous.ext_on (dense_compl_singleton (0:ℝ))
        (hV.continuous_boundary g rest) (hW.continuous_boundary g rest)
        (fun x hx => hall x (Set.mem_compl_singleton_iff.mp hx))
      exact congrFun heq L0

/-! ### A consistency check

The results above are conditional on a volume function satisfying `WPVolumeRecursion`.
Producing such a function in all stable ranges is precisely Mirzakhani's theorem, which we do
not formalize.  The following construction nevertheless shows that the hypotheses used in the
four-holed sphere reduction are consistent: there is a function satisfying the continuity
requirement, both base cases, and every instance of Mirzakhani's recursion with `g = 0` and
`n = 4`; and this function has the four-holed sphere volume predicted above. -/

/-- The sum of the squares of the entries of a multiset of boundary lengths. -/
