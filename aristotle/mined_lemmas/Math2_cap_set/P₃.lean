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

def P₃ : Finset (Idx n) :=
  univ.filter (fun g => ¬ deg n (e₁ n g) ≤ D0 n ∧ ¬ deg n (e₂ n g) ≤ D0 n
    ∧ deg n (e₃ n g) ≤ D0 n)

/-- The first family of slice functions. -/
