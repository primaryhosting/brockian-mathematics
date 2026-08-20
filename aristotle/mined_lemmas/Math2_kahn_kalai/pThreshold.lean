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

noncomputable def pThreshold (F : Finset (Finset α)) : ℝ :=
  sSup {p : ℝ | 0 ≤ p ∧ p ≤ 1 ∧ mu p F ≤ 1 / 2}

omit [Fintype α] [DecidableEq α] in
