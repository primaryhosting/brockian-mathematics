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

lemma minFrag_disjoint {H : Finset (Finset α)} {W S : Finset α} (hS : S ∈ H) :
    Disjoint W (minFrag H W S) := by
  obtain ⟨S', _, _, hEq⟩ := minFrag_eq hS
  rw [hEq]
  exact Finset.disjoint_sdiff

/-- If `V` contains a minimum fragment of `S`, then `W ∪ V` contains an edge of `H`. -/
