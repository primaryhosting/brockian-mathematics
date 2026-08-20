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


lemma vnEntropy_conj_diagonal {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) (v : n → ℝ) :
    vnEntropy (U * Matrix.diagonal (fun i => (v i : ℂ)) * Uᴴ) = shannonEntropy v := by
  rw [vnEntropy, dif_pos (isHermitian_conj_diagonal U v), shannonEntropy]
  exact sum_eigenvalues_conj_diagonal hU v Real.negMulLog _

/-! ### The Holevo bound for jointly diagonalizable ensembles -/

/-- The mutual information obtained from any POVM measurement on a jointly diagonalizable
ensemble is at most the Holevo χ quantity of the ensemble. -/
