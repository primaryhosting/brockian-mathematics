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

lemma Hnext_card_le {H : Finset (Finset α)} {W : Finset α} {m : ℕ} {T : Finset α}
    (hT : T ∈ Hnext H W m) : 2 * T.card < m := by
  simp only [Hnext, Finset.mem_image, Finset.mem_filter] at hT
  obtain ⟨S, ⟨_, hS2⟩, hEq⟩ := hT
  rw [← hEq]
  omega

