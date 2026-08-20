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

lemma minFrag_eq {H : Finset (Finset α)} {W S : Finset α} (hS : S ∈ H) :
    ∃ S' ∈ H, S' ⊆ W ∪ S ∧ minFrag H W S = S' \ W := by
  have h := (minFrag_spec (H := H) (W := W) hS).1
  simp only [cands, Finset.mem_image, Finset.mem_filter] at h
  obtain ⟨S', ⟨hS'H, hS'sub⟩, hEq⟩ := h
  exact ⟨S', hS'H, hS'sub, hEq.symm⟩

