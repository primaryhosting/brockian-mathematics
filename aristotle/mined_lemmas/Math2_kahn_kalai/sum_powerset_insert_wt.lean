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

lemma sum_powerset_insert_wt {x : α} {s : Finset α} (hx : x ∉ s) (p : ℝ)
    (F : Finset α → ℝ) :
    ∑ B ∈ (insert x s).powerset, wtOn (insert x s) p B * F B
      = (1 - p) * (∑ B ∈ s.powerset, wtOn s p B * F B)
        + p * (∑ B ∈ s.powerset, wtOn s p B * F (insert x B)) := by
  rw [Finset.sum_powerset_insert hx, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro B hB
    rw [wtOn_insert_not_mem hx p (mem_powerset.1 hB)]
    ring
  · refine Finset.sum_congr rfl ?_
    intro B hB
    rw [wtOn_insert_mem hx p (mem_powerset.1 hB)]
    ring

/-- The total mass of the `p`-weights on the powerset of `s` is `1`. -/
