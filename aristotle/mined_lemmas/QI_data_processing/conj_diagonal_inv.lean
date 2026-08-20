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

lemma conj_diagonal_inv {U : Matrix n n ℂ} (hU : U * Uᴴ = 1) (hU' : Uᴴ * U = 1) {v : n → ℂ}
    (hv : ∀ k, v k ≠ 0) :
    (U * diagonal v * Uᴴ)⁻¹ = U * diagonal (fun k => (v k)⁻¹) * Uᴴ := by
  refine Matrix.inv_eq_right_inv ?_
  calc U * diagonal v * Uᴴ * (U * diagonal (fun k => (v k)⁻¹) * Uᴴ)
      = U * (diagonal v * (Uᴴ * U) * diagonal (fun k => (v k)⁻¹)) * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hU', Matrix.mul_one, diagonal_mul_diagonal,
          show (fun k => v k * (v k)⁻¹) = fun _ : n => (1 : ℂ) from by
            funext k; exact mul_inv_cancel₀ (hv k),
          show diagonal (fun _ : n => (1 : ℂ)) = 1 from by simp, Matrix.mul_one, hU]

/-- The logarithm of the inverse of a positive definite matrix. -/
