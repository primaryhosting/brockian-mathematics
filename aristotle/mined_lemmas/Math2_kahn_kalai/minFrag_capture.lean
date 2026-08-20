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

lemma minFrag_capture [Fintype α] {H : Finset (Finset α)} {W S : Finset α} (hS : S ∈ H) {V : Finset α}
    (hV : minFrag H W S ⊆ V) : W ∪ V ∈ upset H := by
  obtain ⟨S', hS'H, _, hEq⟩ := minFrag_eq hS
  refine mem_upset.2 ⟨S', hS'H, ?_⟩
  intro x hx
  rw [Finset.mem_union]
  by_cases hxW : x ∈ W
  · exact Or.inl hxW
  · exact Or.inr (hV (by rw [hEq, Finset.mem_sdiff]; exact ⟨hx, hxW⟩))

/-! ### One round of the process -/

/-- The edges of `H` whose minimum fragment is large. -/
