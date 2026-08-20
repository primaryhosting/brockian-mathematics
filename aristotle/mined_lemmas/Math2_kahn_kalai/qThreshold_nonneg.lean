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

lemma qThreshold_nonneg (F : Finset (Finset α)) : 0 ≤ qThreshold F :=
  Real.sSup_nonneg (fun _ hx => hx.1)

omit [DecidableEq α] in
