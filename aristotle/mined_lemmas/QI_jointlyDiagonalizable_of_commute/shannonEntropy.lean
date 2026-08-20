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


noncomputable def shannonEntropy (P : Y → ℝ) : ℝ := ∑ y, Real.negMulLog (P y)

/-- Kullback-Leibler divergence of two finite nonnegative vectors, using the convention
`Real.log 0 = 0`. -/
