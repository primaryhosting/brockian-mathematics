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

noncomputable def cands (H : Finset (Finset α)) (W S : Finset α) : Finset (Finset α) :=
  (H.filter (fun S' => S' ⊆ W ∪ S)).image (fun S' => S' \ W)

