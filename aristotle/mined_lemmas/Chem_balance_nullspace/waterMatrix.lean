/-
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Balance Nullspace

Category: Chemistry
Target: `Chem.balance_nullspace`
Provenance: Aristotle theorem prover (Harmonic)

A chemical reaction is encoded by its stoichiometric matrix `A` (rows = chemical elements,
columns = chemical species, `A i j` = signed number of atoms of element `i` in species `j`).
The reaction *balances* when the species can be given strictly positive amounts so that every
element is conserved.  A priori those amounts are arbitrary positive numbers (a chemist solving
the linear system by Gaussian elimination gets rational ones), whereas a chemical equation must
be written with positive *integer* coefficients.

`Chem.balance_nullspace` says these two notions agree: a reaction balances if and only if its
stoichiometric matrix has a strictly positive integer null vector.  The nontrivial direction
clears denominators, multiplying a positive rational solution by the product of its
denominators.
-/

namespace Chem

variable {m n : ℕ}

/-- A reaction with stoichiometric matrix `A` *balances* if strictly positive (rational)
amounts of the species can be chosen so that every element is conserved. -/

def waterMatrix : Matrix (Fin 2) (Fin 3) ℤ := !![2, 0, -2; 0, 2, -1]

/-- The synthesis of water balances: `2 H₂ + O₂ → 2 H₂O`. -/
