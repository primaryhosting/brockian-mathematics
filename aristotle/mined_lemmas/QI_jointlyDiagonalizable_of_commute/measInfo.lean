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


noncomputable def measInfo (p : X → ℝ) (ρ : X → Matrix n n ℂ) (E : Y → Matrix n n ℂ) : ℝ :=
  shannonEntropy (fun y => ∑ x, p x * outcomeProb (ρ x) (E y))
    - ∑ x, p x * shannonEntropy (fun y => outcomeProb (ρ x) (E y))

/-- The accessible information of an ensemble: the supremum of the mutual information over all
POVMs (with an arbitrary finite number of outcomes). -/
