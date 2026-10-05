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

def S₂ (a : Exp n) (x z : Fin n → ZMod 3) : ZMod 3 :=
  ∑ g ∈ (P₂ n).filter (fun g => e₂ n g = a), cprod n g * mon n (e₁ n g) x * mon n (e₃ n g) z

/-- The third family of slice functions. -/
