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

lemma conj_diagonal_add (U : Matrix n n ℂ) (v w : n → ℂ) :
    U * diagonal v * Uᴴ + U * diagonal w * Uᴴ = U * diagonal (v + w) * Uᴴ := by
  rw [← Matrix.add_mul, ← Matrix.mul_add]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h]

