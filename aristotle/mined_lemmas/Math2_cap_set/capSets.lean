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

def capSets (n : ℕ) : Finset (Finset (Fin n → ZMod 3)) :=
  (univ : Finset (Finset (Fin n → ZMod 3))).filter
    (fun A : Finset (Fin n → ZMod 3) => ThreeAPFree (A : Set (Fin n → ZMod 3)))

/-- The largest size of a 3AP-free subset of `𝔽₃ⁿ`. -/
