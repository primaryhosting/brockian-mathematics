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


noncomputable def avgState (p : X → ℝ) (ρ : X → Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ x, (p x : ℂ) • ρ x

/-- The probability of the outcome corresponding to the POVM element `E` in the state `ρ`. -/
