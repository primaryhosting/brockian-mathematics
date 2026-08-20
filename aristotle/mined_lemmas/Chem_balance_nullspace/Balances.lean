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

def Balances (A : Matrix (Fin m) (Fin n) ℤ) (x : Fin n → ℤ) : Prop :=
  ∀ i, ∑ j, A i j * x j = 0

/-- A reaction is *balanceable* if some vector of strictly positive integer coefficients
balances it. -/
