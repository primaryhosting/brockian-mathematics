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


noncomputable def holevoChi (p : X → ℝ) (ρ : X → Matrix n n ℂ) : ℝ :=
  vnEntropy (avgState p ρ) - ∑ x, p x * vnEntropy (ρ x)

/-- The mutual information between the classical label `X` and the outcome of the measurement
`E` performed on the ensemble. -/
