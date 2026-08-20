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

lemma sum_wt (p : ℝ) : ∑ A : Finset α, wt p A = 1 := by
  have h : (Finset.univ : Finset (Finset α)) = (Finset.univ : Finset α).powerset := by
    rw [Finset.powerset_univ]
  rw [h]
  exact sum_wtOn _ p

/-- The union of independent `a`- and `b`-random subsets is an `(a+b-a*b)`-random subset. -/
