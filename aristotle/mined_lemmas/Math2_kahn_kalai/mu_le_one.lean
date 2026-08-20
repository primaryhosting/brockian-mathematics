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

lemma mu_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F : Finset (Finset α)) : mu p F ≤ 1 := by
  rw [← sum_wt (α := α) p]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
    (fun A _ _ => wt_nonneg hp0 hp1 A)

