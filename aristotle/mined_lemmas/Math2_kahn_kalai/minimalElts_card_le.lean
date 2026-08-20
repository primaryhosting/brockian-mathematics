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

lemma minimalElts_card_le {F : Finset (Finset α)} {S : Finset α} (hS : S ∈ minimalElts F) :
    S.card ≤ ell F :=
  le_trans (Finset.le_sup hS) (le_max_right _ _)

