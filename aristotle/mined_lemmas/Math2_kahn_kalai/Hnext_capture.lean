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

lemma Hnext_capture [Fintype α] {H : Finset (Finset α)} {W : Finset α} {m : ℕ} {V : Finset α}
    (hV : V ∈ upset (Hnext H W m)) : W ∪ V ∈ upset H := by
  rw [mem_upset] at hV
  obtain ⟨T, hT, hTV⟩ := hV
  simp only [Hnext, Finset.mem_image, Finset.mem_filter] at hT
  obtain ⟨S, ⟨hSH, _⟩, hEq⟩ := hT
  exact minFrag_capture hSH (by rw [hEq]; exact hTV)

/-- Combining a cover of the next-round hypergraph with the fragment cover gives a cover
of `H`. -/
