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

lemma exists_diagonalization_pos {A : Matrix n n ℂ} (hA : A.PosDef) :
    ∃ (U : Matrix n n ℂ) (d : n → ℝ), U * Uᴴ = 1 ∧ Uᴴ * U = 1 ∧ (∀ k, 0 < d k) ∧
      A = U * diagonal (fun i => ((d i : ℝ) : ℂ)) * Uᴴ :=
  ⟨_, hA.isHermitian.eigenvalues, eigen_unitary _, eigen_unitary' _, hA.eigenvalues_pos,
    eigen_decomp _⟩

