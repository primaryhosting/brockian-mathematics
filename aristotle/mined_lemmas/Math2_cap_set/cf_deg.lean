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

lemma cf_deg : ∀ t : Fin 3 × Fin 3 × Fin 3, cf t ≠ 0 →
    (t.1 : ℕ) + (t.2.1 : ℕ) + (t.2.2 : ℕ) ≤ 2 := by decide

variable (n : ℕ)

/-- Exponent vectors with all exponents `< 3`. -/
abbrev Exp := Fin n → Fin 3

/-- The (reduced) monomial attached to an exponent vector. -/
