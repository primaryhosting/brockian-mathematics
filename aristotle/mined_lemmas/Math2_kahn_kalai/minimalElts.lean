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

noncomputable def minimalElts (F : Finset (Finset α)) : Finset (Finset α) :=
  F.filter (fun A => ∀ B ∈ F, B ⊆ A → B = A)

/-- `ell F` is the maximum of `2` and the largest size of a minimal element of `F`. -/
