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

lemma dens_le_mul (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (k : ℕ) : dens r k ≤ k * r := by
  induction k with
  | zero => simp [dens]
  | succ k ih =>
      rw [dens_succ]
      have h1 : 0 ≤ dens r k := dens_nonneg hr0 hr1 k
      have : r * dens r k ≥ 0 := mul_nonneg hr0 h1
      push_cast
      nlinarith

/-- The bound on the total expected cover cost, as a function of the size bound. -/
