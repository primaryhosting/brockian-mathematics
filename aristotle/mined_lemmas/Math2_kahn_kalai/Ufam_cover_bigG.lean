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

lemma Ufam_cover_bigG (H : Finset (Finset α)) (W : Finset α) (m : ℕ) :
    IsCover (bigG H W m) (Ufam H W m) := by
  intro S hS
  refine ⟨minFrag H W S, ?_, ?_⟩
  · exact Finset.mem_image_of_mem _ hS
  · exact minFrag_subset (Finset.mem_filter.1 hS).1

