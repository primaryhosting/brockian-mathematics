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

lemma cost_union_le {p : ℝ} (hp : 0 ≤ p) (U V : Finset (Finset α)) :
    cost p (U ∪ V) ≤ cost p U + cost p V := by
  classical
  have h : U ∪ V = U ∪ (V \ U) := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff]; tauto
  simp only [cost]
  rw [h, Finset.sum_union (Finset.disjoint_sdiff)]
  have h2 : ∑ u ∈ V \ U, p ^ u.card ≤ ∑ u ∈ V, p ^ u.card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset) (fun u _ _ => pow_nonneg hp _)
  linarith

/-- `H` is `p`-small: it has a cover of cost at most `1/2`. -/
