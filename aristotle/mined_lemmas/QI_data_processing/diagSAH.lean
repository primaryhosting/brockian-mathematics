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

noncomputable def diagSAH : (n → ℂ) →⋆ₐ[ℂ] Matrix n n ℂ where
  toFun := Matrix.diagonal
  map_one' := by simp
  map_mul' x y := by simp [Matrix.diagonal_mul_diagonal]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.diagonal_add]
  commutes' r := by
    ext i j; by_cases h : i = j <;>
      simp [Matrix.diagonal, h, Algebra.algebraMap_eq_smul_one]
  map_star' x := by ext i j; by_cases h : i = j <;> simp [Matrix.diagonal, h, eq_comm]

/-- The continuous functional calculus of a real diagonal matrix is diagonal. -/
