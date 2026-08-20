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


lemma sum_eigenvalues_conj_diagonal {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    (v : n → ℝ) (f : ℝ → ℝ)
    (hH : (U * Matrix.diagonal (fun i => (v i : ℂ)) * Uᴴ).IsHermitian) :
    ∑ i, f (hH.eigenvalues i) = ∑ i, f (v i) := by
  classical
  have hUU : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff' (A := U)).1 hU
  -- the characteristic polynomial is that of the diagonal matrix
  have hchar : (U * Matrix.diagonal (fun i => (v i : ℂ)) * Uᴴ).charpoly
      = ∏ i, (Polynomial.X - Polynomial.C ((v i : ℂ))) := by
    rw [mul_assoc, Matrix.charpoly_mul_comm, mul_assoc, hUU, mul_one, Matrix.charpoly_diagonal]
  have hroots : (U * Matrix.diagonal (fun i => (v i : ℂ)) * Uᴴ).charpoly.roots
      = Multiset.map (fun i => ((v i : ℂ))) Finset.univ.val := by
    rw [hchar, Finset.prod_eq_multiset_prod,
      show (Multiset.map (fun i => Polynomial.X - Polynomial.C ((v i : ℂ))) Finset.univ.val)
        = Multiset.map (fun a => Polynomial.X - Polynomial.C a)
            (Multiset.map (fun i => ((v i : ℂ))) Finset.univ.val) by
        rw [Multiset.map_map]; rfl]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  have hmul : Multiset.map (RCLike.ofReal ∘ hH.eigenvalues) (Finset.univ (α := n)).val
      = Multiset.map (fun i => ((v i : ℂ))) Finset.univ.val := by
    rw [← hH.roots_charpoly_eq_eigenvalues, hroots]
  have := congrArg (Multiset.map (fun z : ℂ => f z.re)) hmul
  rw [Multiset.map_map, Multiset.map_map] at this
  simpa [Function.comp] using congrArg Multiset.sum this

