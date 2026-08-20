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

theorem quadForm_conj_diagonal (U : Matrix n n ℂ) (v : n → ℂ) (x : n → ℂ) :
    star x ⬝ᵥ ((U * diagonal v * Uᴴ) *ᵥ x)
      = ∑ k, v k * (starRingEnd ℂ ((Uᴴ *ᵥ x) k) * ((Uᴴ *ᵥ x) k)) := by
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    show star x ᵥ* U = star (Uᴴ *ᵥ x) by rw [Matrix.star_mulVec]; simp]
  simp [Matrix.mulVec_diagonal, dotProduct, mul_comm, mul_assoc]

/-- The squared moduli of the coordinates of `x` in the eigenbasis of `A`. -/
