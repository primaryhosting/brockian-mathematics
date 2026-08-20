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

lemma cost_nonneg {p : ℝ} (hp : 0 ≤ p) (U : Finset (Finset α)) : 0 ≤ cost p U :=
  Finset.sum_nonneg fun _ _ => pow_nonneg hp _

omit [Fintype α] in
