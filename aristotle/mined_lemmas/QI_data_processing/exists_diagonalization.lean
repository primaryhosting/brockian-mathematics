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

lemma exists_diagonalization {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ∃ (U : Matrix n n ℂ) (d : n → ℝ), U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧
      A = U * diagonal (fun i => ((d i : ℝ) : ℂ)) * Uᴴ :=
  ⟨_, hA.eigenvalues, eigen_unitary hA, eigen_unitary' hA, eigen_decomp hA⟩

/-- Existence of a unitary diagonalization with positive eigenvalues. -/
