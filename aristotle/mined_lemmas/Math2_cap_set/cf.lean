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

def cf : Fin 3 × Fin 3 × Fin 3 → ZMod 3 := fun t =>
  match t with
  | (0, 0, 0) => 1
  | (2, 0, 0) => 2
  | (0, 2, 0) => 2
  | (0, 0, 2) => 2
  | (1, 1, 0) => 1
  | (0, 1, 1) => 1
  | (1, 0, 1) => 1
  | _ => 0

