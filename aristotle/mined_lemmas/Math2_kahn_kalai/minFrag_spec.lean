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

lemma minFrag_spec {H : Finset (Finset α)} {W S : Finset α} (hS : S ∈ H) :
    minFrag H W S ∈ cands H W S ∧
      ∀ T ∈ cands H W S, (minFrag H W S).card ≤ T.card := by
  have h := cands_nonempty (H := H) (W := W) hS
  rw [minFrag, dif_pos h]
  have := Classical.choose_spec (Finset.exists_min_image (cands H W S) Finset.card h)
  obtain ⟨h1, h2⟩ := this
  exact ⟨h1, h2⟩

/-- The defining property of a minimum fragment: it is `S' \ W` for some edge `S'` inside
`W ∪ S`. -/
