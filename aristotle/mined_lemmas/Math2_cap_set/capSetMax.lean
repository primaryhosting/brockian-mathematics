import RequestProject.CapExpand

/-!
# The Ellenberg–Gijswijt bound

Combining the slice-rank bound with the polynomial expansion gives
`|A| ≤ 3 · #{exponent vectors of degree ≤ 2n/3}` for every 3AP-free `A ⊆ 𝔽₃ⁿ`.
-/

open scoped BigOperators
open Finset

namespace CapSetAux

/-- In `𝔽₃ⁿ`, a 3AP-free set contains no nontrivial triple summing to zero. -/

def capSetMax (n : ℕ) : ℕ := (capSets n).sup Finset.card

/-- The cap-set theorem in asymptotic form: the maximal size of a 3AP-free subset of
`𝔽₃ⁿ` is `o(3ⁿ)`. -/
