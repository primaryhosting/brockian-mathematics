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

lemma kron_mulVecm (A : Matrix n n ℂ) (B : Matrix m m ℂ) (X : Matrix n m ℂ) :
    (A ⊗ₖ Bᵀ) *ᵥ vecm X = vecm (A * X * B) := by
  funext p
  simp [vecm, mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply, Finset.mul_sum, mul_comm, mul_left_comm]
  rw [Finset.sum_comm]

/-! ### The modular operator -/

/-- The (relative) modular operator `σ ⊗ (ρ⁻¹)ᵀ`, acting on vectorized matrices by
`X ↦ σ X ρ⁻¹`. -/
