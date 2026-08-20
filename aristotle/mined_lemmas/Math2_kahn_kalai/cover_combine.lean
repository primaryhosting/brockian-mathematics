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

lemma cover_combine {H : Finset (Finset α)} {W : Finset α} {m : ℕ} {V : Finset (Finset α)}
    (hV : IsCover (Hnext H W m) V) : IsCover H (V ∪ Ufam H W m) := by
  intro S hS
  by_cases hbig : m ≤ 2 * (minFrag H W S).card
  · refine ⟨minFrag H W S, ?_, minFrag_subset hS⟩
    refine Finset.mem_union_right _ ?_
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hS, hbig⟩)
  · have hmem : minFrag H W S ∈ Hnext H W m :=
      Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hS, hbig⟩)
    obtain ⟨v, hv, hvsub⟩ := hV _ hmem
    exact ⟨v, Finset.mem_union_left _ hv, hvsub.trans (minFrag_subset hS)⟩

/-! ### The canonical edge inside a set -/

/-- A canonical edge of `H` inside `Z`, if there is one. -/
