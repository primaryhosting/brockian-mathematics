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

noncomputable def qThreshold (F : Finset (Finset α)) : ℝ :=
  sSup {q : ℝ | 0 ≤ q ∧ q ≤ 1 ∧ IsSmall q F}

/-- The threshold: the largest `p` for which `mu p F ≤ 1/2`. -/
