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

lemma cf_expand : ∀ u v w : ZMod 3, (if u + v + w = 0 then (1 : ZMod 3) else 0)
    = ∑ t : Fin 3 × Fin 3 × Fin 3, cf t * u ^ (t.1 : ℕ) * v ^ (t.2.1 : ℕ) * w ^ (t.2.2 : ℕ) := by
  decide

