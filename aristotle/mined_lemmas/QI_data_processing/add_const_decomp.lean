import RequestProject.Kron

/-!
# Vectorization, the modular operator and relative entropy

We vectorize matrices, express the relative entropy `Tr ρ log ρ - Tr ρ log σ` as (minus) a
quadratic form of `log (σ ⊗ (ρ⁻¹)ᵀ)` at the vectorization of `√ρ`, and record the
variational ("completing the square") characterization of resolvent quadratic forms.
-/

open Matrix
open scoped Kronecker ComplexOrder BigOperators MatrixOrder

namespace QI

variable {n m N : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype N] [DecidableEq N]

/-! ### Vectorization -/

/-- Vectorization of a matrix: the vector of all its entries, indexed by pairs. -/

lemma add_const_decomp {A : Matrix n n ℂ} (hA : A.IsHermitian) (t : ℝ) :
    A + (t : ℂ) • 1 = ((hA.eigenvectorUnitary : Matrix n n ℂ)) *
      diagonal (fun k => ((hA.eigenvalues k + t : ℝ) : ℂ)) *
      ((hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ := by
  conv_lhs => rw [eigen_decomp hA, smul_one_conj _ (eigen_unitary hA) ((t : ℝ) : ℂ)]
  have hfun : ((fun i => ((hA.eigenvalues i : ℝ) : ℂ)) + fun _ : n => ((t : ℝ) : ℂ))
      = fun k => ((hA.eigenvalues k + t : ℝ) : ℂ) := by
    funext k; simp
  rw [conj_diagonal_add, hfun]

/-- Spectral form of the resolvent. -/
