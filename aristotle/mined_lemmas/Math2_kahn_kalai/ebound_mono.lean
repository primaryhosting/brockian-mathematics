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

lemma ebound_mono {m m' : ℕ} (h : m' ≤ m) : ebound m' ≤ ebound m := by
  have : (1 / 9 : ℝ) ^ m ≤ (1 / 9 : ℝ) ^ m' :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) h
  simp only [ebound]; linarith

