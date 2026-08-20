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

lemma upset_minimalElts_subset {F : Finset (Finset α)} (hF : IsUp F) :
    upset (minimalElts F) ⊆ F := by
  intro A hA
  rw [mem_upset] at hA
  obtain ⟨S, hS, hSA⟩ := hA
  rw [minimalElts, Finset.mem_filter] at hS
  exact hF S hS.1 A hSA

/-- The expectation threshold: the largest `q` for which `F` is `q`-small. -/
