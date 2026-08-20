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

theorem mem_ker_mulVecLin_iff (A : Matrix (Fin m) (Fin n) ℚ) (x : Fin n → ℚ) :
    x ∈ LinearMap.ker (Matrix.mulVecLin A) ↔ Conserves A x := by
  simp [Conserves, Matrix.mulVec, dotProduct, funext_iff]

/-- Clearing denominators: a finite family of positive rationals can be scaled by a single
positive integer to a family of positive integers. -/
