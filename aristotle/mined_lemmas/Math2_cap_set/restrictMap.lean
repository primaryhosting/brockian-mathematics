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

def restrictMap (W : Submodule F (X → F)) (S : Finset X) : W →ₗ[F] (S → F) where
  toFun u := fun x => (u : X → F) (x : X)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- A subspace `W` of `X → F` contains an element whose support has size at least
`finrank W`. -/
