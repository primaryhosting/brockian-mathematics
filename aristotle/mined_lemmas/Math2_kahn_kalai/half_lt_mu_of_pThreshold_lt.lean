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

lemma half_lt_mu_of_pThreshold_lt {F : Finset (Finset α)} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (h : pThreshold F < p) : 1 / 2 < mu p F := by
  by_contra hcon
  push_neg at hcon
  have : p ≤ pThreshold F := le_csSup (pThreshold_bddAbove F) ⟨hp0, hp1, hcon⟩
  linarith

omit [Fintype α] [DecidableEq α] in
