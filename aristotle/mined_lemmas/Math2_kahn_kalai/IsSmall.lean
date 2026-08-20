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

def IsSmall (p : ℝ) (H : Finset (Finset α)) : Prop :=
  ∃ U : Finset (Finset α), IsCover H U ∧ cost p U ≤ 1 / 2

end KahnKalai

/-
The iteration: repeatedly extracting minimum fragments halves the size bound of the
hypergraph, and the accumulated cover cost stays bounded.
-/
import RequestProject.KeyLemma

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The density of a union of `k` independent `r`-random sets. -/
