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

lemma cands_nonempty {H : Finset (Finset α)} {W S : Finset α} (hS : S ∈ H) :
    (cands H W S).Nonempty := by
  refine ⟨S \ W, ?_⟩
  simp only [cands, Finset.mem_image, Finset.mem_filter]
  exact ⟨S, ⟨hS, Finset.subset_union_right⟩, rfl⟩

/-- A minimum `(S,W)`-fragment: a smallest set of the form `S' \ W` with `S' ∈ H`
and `S' ⊆ W ∪ S`. -/
