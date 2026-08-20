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

lemma isUp_upset (H : Finset (Finset α)) : IsUp (upset H) :=
  fun _ hA _ hAB => upset_upward_closed hA hAB

/-- Monotonicity of `mu` in the density, for upward closed families. -/
