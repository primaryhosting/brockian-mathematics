import Mathlib

/-!
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

variable {m n : ℕ}

/-- `A` is the *stoichiometric matrix* of a reaction: rows are elements, columns are chemical
species, and `A i j` is the (signed) number of atoms of element `i` in species `j`.  A vector
`x` of stoichiometric coefficients *conserves* every element when each row of `A` is orthogonal
to `x`. -/

def Conserves (A : Matrix (Fin m) (Fin n) ℚ) (x : Fin n → ℚ) : Prop :=
  ∀ i, ∑ j, A i j * x j = 0

/-- A reaction *balances* when some assignment of strictly positive (rational) stoichiometric
coefficients conserves every element. -/
