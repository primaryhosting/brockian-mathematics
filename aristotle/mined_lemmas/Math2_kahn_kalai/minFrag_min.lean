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

lemma minFrag_min {H : Finset (Finset α)} {W S : Finset α} (hS : S ∈ H) {S' : Finset α}
    (hS'H : S' ∈ H) (hS'sub : S' ⊆ W ∪ S) : (minFrag H W S).card ≤ (S' \ W).card := by
  refine (minFrag_spec hS).2 _ ?_
  simp only [cands, Finset.mem_image, Finset.mem_filter]
  exact ⟨S', ⟨hS'H, hS'sub⟩, rfl⟩

