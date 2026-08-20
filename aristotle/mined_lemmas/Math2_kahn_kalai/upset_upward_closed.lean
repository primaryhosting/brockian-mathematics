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

lemma upset_upward_closed {H : Finset (Finset α)} {A B : Finset α} (hA : A ∈ upset H)
    (hAB : A ⊆ B) : B ∈ upset H := by
  rw [mem_upset] at hA ⊢
  obtain ⟨S, hS, hSA⟩ := hA
  exact ⟨S, hS, hSA.trans hAB⟩

/-- A family `F` is upward closed. -/
