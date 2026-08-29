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

def deg (a : Exp n) : ℕ := ∑ i, (a i : ℕ)

/-- Index type for the terms of the triple expansion. -/
abbrev Idx := Fin n → Fin 3 × Fin 3 × Fin 3

/-- The coefficient of the term indexed by `g`. -/
