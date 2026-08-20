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

lemma sum_wtOn (s : Finset α) (p : ℝ) : ∑ A ∈ s.powerset, wtOn s p A = 1 := by
  have h := Finset.prod_add (fun _ : α => p) (fun _ : α => (1 - p)) s
  simp only [Finset.prod_const] at h
  rw [show p + (1 - p) = 1 by ring] at h
  simp only [one_pow] at h
  rw [h]
  refine Finset.sum_congr rfl ?_
  intro A hA
  rw [Finset.mem_powerset] at hA
  rw [wtOn, Finset.card_sdiff_of_subset hA]

/-- The union of independent `a`- and `b`-random subsets of `s` is an
`(a + b - a*b)`-random subset of `s`. -/
