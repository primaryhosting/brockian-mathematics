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


lemma psd_diag_nonneg {M : Matrix n n ℂ} (h : M.PosSemidef) (i : n) : 0 ≤ (M i i).re := by
  have := h.re_dotProduct_nonneg (Pi.single i 1)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq'] using this

