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


noncomputable def accessibleInfo (p : X → ℝ) (ρ : X → Matrix n n ℂ) : ℝ :=
  sSup {I : ℝ | ∃ (m : ℕ) (E : Fin m → Matrix n n ℂ), IsPOVM E ∧ I = measInfo p ρ E}

/-- An ensemble is *jointly diagonalizable* when all its states are diagonal in one common
orthonormal basis; equivalently (for Hermitian matrices), when they commute pairwise. -/
