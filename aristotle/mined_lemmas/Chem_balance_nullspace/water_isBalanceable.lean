import Mathlib

/-!
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Finset

variable {m n : ℕ}

/-- `Balances A x` says that the (signed) stoichiometric coefficient vector `x` balances the
reaction whose stoichiometric matrix is `A`: for every element `i` (row of `A`), the total
number of atoms of that element created minus destroyed is zero. -/

theorem water_isBalanceable :
    IsBalanceable (Matrix.of ![![2, 0, -2], ![0, 2, -1]] : Matrix (Fin 2) (Fin 3) ℤ) :=
  ⟨![2, 1, 2], by decide, fun i => by fin_cases i <;> decide⟩

/-- A concrete unbalanceable "reaction": `H₂ → O₂` (hydrogen on both sides is impossible to
cancel because the H row is nonnegative and nonzero). -/
