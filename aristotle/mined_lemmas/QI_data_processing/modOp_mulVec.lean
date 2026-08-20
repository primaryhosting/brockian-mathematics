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

lemma modOp_mulVec (σ ρ : Matrix n n ℂ) (X : Matrix n n ℂ) :
    modOp σ ρ *ᵥ vecm X = vecm (σ * X * ρ⁻¹) := kron_mulVecm _ _ _

/-! ### Relative entropy -/

/-- Umegaki relative entropy `Tr ρ log ρ - Tr ρ log σ`. -/
