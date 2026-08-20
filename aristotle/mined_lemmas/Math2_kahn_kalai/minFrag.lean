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

noncomputable def minFrag (H : Finset (Finset α)) (W S : Finset α) : Finset α :=
  if h : (cands H W S).Nonempty then
    Classical.choose (Finset.exists_min_image (cands H W S) Finset.card h)
  else ∅

