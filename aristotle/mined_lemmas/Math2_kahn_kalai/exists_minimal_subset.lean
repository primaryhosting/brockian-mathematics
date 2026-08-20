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

lemma exists_minimal_subset {F : Finset (Finset α)} {S : Finset α} (hS : S ∈ F) :
    ∃ A ∈ minimalElts F, A ⊆ S := by
  obtain ⟨A, hA, hAmin⟩ :=
    Finset.exists_min_image (F.filter (fun B => B ⊆ S)) Finset.card
      ⟨S, Finset.mem_filter.2 ⟨hS, Finset.Subset.refl S⟩⟩
  rw [Finset.mem_filter] at hA
  refine ⟨A, ?_, hA.2⟩
  rw [minimalElts, Finset.mem_filter]
  refine ⟨hA.1, ?_⟩
  intro B hB hBA
  have hmem : B ∈ F.filter (fun B => B ⊆ S) :=
    Finset.mem_filter.2 ⟨hB, hBA.trans hA.2⟩
  exact Finset.eq_of_subset_of_card_le hBA (hAmin B hmem)

