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

lemma wt_union_bound {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) {W U : Finset α}
    (hd : Disjoint W U) {p : ℝ} (hp : 0 ≤ p) :
    wt r W * p ^ U.card ≤ wt r (W ∪ U) * (p / r) ^ U.card := by
  have hcard : (W ∪ U).card = W.card + U.card := Finset.card_union_of_disjoint hd
  have hn : W.card + U.card ≤ Fintype.card α := by
    rw [← hcard]; exact Finset.card_le_univ _
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card α - W.card = k + U.card :=
    ⟨Fintype.card α - W.card - U.card, by omega⟩
  have hk2 : Fintype.card α - (W.card + U.card) = k := by omega
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hX : 0 ≤ r ^ W.card * (1 - r) ^ k * p ^ U.card := by
    have : (0:ℝ) ≤ 1 - r := by linarith
    positivity
  have hLHS : wt r W * p ^ U.card
      = (r ^ W.card * (1 - r) ^ k * p ^ U.card) * (1 - r) ^ U.card := by
    simp only [wt, wtOn, Finset.card_univ, hk]
    rw [pow_add]; ring
  have hRHS : wt r (W ∪ U) * (p / r) ^ U.card
      = r ^ W.card * (1 - r) ^ k * p ^ U.card := by
    simp only [wt, wtOn, Finset.card_univ, hcard, hk2]
    rw [div_pow, pow_add]
    field_simp
  rw [hLHS, hRHS]
  have h1 : (1 - r) ^ U.card ≤ 1 :=
    pow_le_one₀ (by linarith) (by linarith)
  nlinarith

