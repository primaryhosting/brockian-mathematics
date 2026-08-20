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

lemma ebound_le (m : ℕ) : ebound m ≤ 1 / 8 := by
  have : (0:ℝ) ≤ (1 / 9 : ℝ) ^ m := by positivity
  simp only [ebound]; linarith

