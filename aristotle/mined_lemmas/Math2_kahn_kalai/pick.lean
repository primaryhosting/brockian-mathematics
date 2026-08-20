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

noncomputable def pick (H : Finset (Finset α)) (Z : Finset α) : Finset α :=
  if h : (H.filter (fun S => S ⊆ Z)).Nonempty then h.choose else ∅

