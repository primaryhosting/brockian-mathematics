import Mathlib
import RequestProject.Holevo

/-!
# Simultaneous diagonalization of a commuting family of Hermitian matrices

The main result `QI.jointlyDiagonalizable_of_commute` shows that a family of pairwise commuting
Hermitian matrices is diagonal in a common orthonormal basis, i.e. satisfies
`QI.JointlyDiagonalizable`.
-/

open Matrix LinearMap
open scoped Function

namespace QI

variable {n X : Type*} [Fintype n] [DecidableEq n]


lemma trace_diagonal_mul (d : n → ℂ) (M : Matrix n n ℂ) :
    (Matrix.diagonal d * M).trace = ∑ i, d i * M i i := by
  simp [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]

/-- The eigenvalues of `U * diagonal v * Uᴴ` are the entries of `v`, up to a permutation; hence
any sum `∑ f (eigenvalue)` can be computed from `v`. -/
