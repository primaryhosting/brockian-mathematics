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

lemma qThreshold_bddAbove (F : Finset (Finset α)) :
    BddAbove {q : ℝ | 0 ≤ q ∧ q ≤ 1 ∧ IsSmall q F} :=
  ⟨1, fun _ hx => hx.2.1⟩

end KahnKalai

namespace Math2

open KahnKalai

/-- **The Kahn-Kalai conjecture** (Park-Pham theorem): the threshold of an increasing
property is at most a universal constant times its expectation threshold times `log ℓ`,
where `ℓ` is the maximum of `2` and the size of a largest minimal element.

Here `mu p F = ∑_{A ∈ F} p^{|A|} (1-p)^{n-|A|}` is the product measure of `F`, the
threshold `pThreshold F` is the supremum of all `p ∈ [0,1]` with `mu p F ≤ 1/2`, and the
expectation threshold `qThreshold F` is the supremum of all `q ∈ [0,1]` such that `F` admits
a cover `U` (a family such that every member of `F` contains a member of `U`) with
`∑_{u ∈ U} q^{|u|} ≤ 1/2`. -/
