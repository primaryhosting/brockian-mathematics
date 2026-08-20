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

lemma dens_le_one {r : ℝ} (hr1 : r ≤ 1) (k : ℕ) : dens r k ≤ 1 := by
  have : 0 ≤ (1 - r) ^ k := pow_nonneg (by linarith) _
  simp only [dens]; linarith

