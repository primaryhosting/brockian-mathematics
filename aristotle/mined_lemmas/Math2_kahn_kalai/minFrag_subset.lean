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

lemma minFrag_subset {H : Finset (Finset α)} {W S : Finset α} (hS : S ∈ H) :
    minFrag H W S ⊆ S := by
  obtain ⟨S', _, hsub, hEq⟩ := minFrag_eq hS
  rw [hEq]
  intro x hx
  rw [Finset.mem_sdiff] at hx
  rcases Finset.mem_union.1 (hsub hx.1) with h | h
  · exact absurd h hx.2
  · exact h

