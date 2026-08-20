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

lemma mu_eq_sum_ite (p : ℝ) (F : Finset (Finset α)) :
    mu p F = ∑ A : Finset α, if A ∈ F then wt p A else 0 := by
  rw [mu, ← Finset.sum_filter]
  exact Finset.sum_congr (by ext A; simp) (fun _ _ => rfl)

omit [DecidableEq α] in
