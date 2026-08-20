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


lemma isHermitian_conj_diagonal (U : Matrix n n ℂ) (v : n → ℝ) :
    (U * Matrix.diagonal (fun i => (v i : ℂ)) * Uᴴ).IsHermitian := by
  have hD : (Matrix.diagonal (fun i => (v i : ℂ))).IsHermitian := by
    apply Matrix.isHermitian_diagonal_iff.2
    intro i
    show star ((v i : ℂ)) = _
    exact Complex.conj_ofReal _
  have := Matrix.isHermitian_conjTranspose_mul_mul (A := Matrix.diagonal (fun i => (v i : ℂ)))
    Uᴴ hD
  simpa using this

