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

lemma mu_eq_sum_indicator (p : ℝ) (F : Finset (Finset α)) :
    mu p F = ∑ C : Finset α, wt p C * (if C ∈ F then (1:ℝ) else 0) := by
  rw [mu_eq_sum_ite]
  exact Finset.sum_congr rfl (fun C _ => by by_cases h : C ∈ F <;> simp [h])

/-- The main induction. If `H` is `m`-bounded with `m < 2^k`, and every cover of `H` costs
at least `θ`, then a `dens r k`-random set lies in `⟨H⟩` with probability at least
`1 - ebound m / θ`. -/
