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

lemma Kconst_log_two : Kconst * Real.log 2 = 648 := by
  rw [Kconst]
  field_simp

/-! ### The main theorem for hypergraphs -/

/-- **Kahn-Kalai, hypergraph form.** If the `m`-bounded hypergraph `H` (with `m ≥ 2`) is not
`p`-small, then a `ρ`-random set lies in the up-set of `H` with probability more than `1/2`,
as soon as `ρ ≥ Kconst * p * log m`. -/
