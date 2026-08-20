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

lemma cover_of_cover_minimalElts {F : Finset (Finset α)} {U : Finset (Finset α)}
    (hU : IsCover (minimalElts F) U) : IsCover F U := by
  intro S hS
  obtain ⟨A, hA, hAS⟩ := exists_minimal_subset hS
  obtain ⟨u, hu, huA⟩ := hU A hA
  exact ⟨u, hu, huA.trans hAS⟩

