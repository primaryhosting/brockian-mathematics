/-
Minimum fragments (Park-Pham) and the key lemma: the cover built from the large
minimum fragments has small expected cost.
-/
import RequestProject.Basic

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α]

/-! ### Minimum fragments -/

/-- The candidate fragments of `S` relative to `W`: the sets `S' \ W` for edges `S'` of `H`
contained in `W ∪ S`. -/

lemma mu_le_half_of_lt_pThreshold {F : Finset (Finset α)} (hF : IsUp F) {p : ℝ}
    (hp0 : 0 ≤ p) (h : p < pThreshold F) : mu p F ≤ 1 / 2 := by
  rcases Set.eq_empty_or_nonempty {p : ℝ | 0 ≤ p ∧ p ≤ 1 ∧ mu p F ≤ 1 / 2} with h0 | hne
  · rw [pThreshold, h0, Real.sSup_empty] at h
    linarith
  · obtain ⟨p', hp', hlt⟩ := exists_lt_of_lt_csSup hne h
    exact le_trans (mu_mono hp0 (le_of_lt hlt) hp'.2.1 hF) hp'.2.2

omit [DecidableEq α] in
/-- Above the threshold, the measure exceeds `1/2`. -/
