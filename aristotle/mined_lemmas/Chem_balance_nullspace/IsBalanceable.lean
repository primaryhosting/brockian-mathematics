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

def IsBalanceable (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∃ x : Fin n → ℤ, (∀ j, 0 < x j) ∧ Balances A x

/-- **Balance nullspace.** A chemical reaction balances (with strictly positive integer
coefficients) if and only if its stoichiometric matrix has a strictly positive integer vector
in its kernel (null space). -/
