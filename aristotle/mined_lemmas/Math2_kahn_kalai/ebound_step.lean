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

lemma ebound_step {m : ℕ} (hm : 1 ≤ m) : (1 / 9 : ℝ) ^ m + ebound (m - 1) = ebound m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  simp only [ebound, Nat.add_sub_cancel, pow_succ]
  ring

/-- The measure as a sum of indicators. -/
