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

lemma resolvent_decomp {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (hpos : ∀ k, 0 ≤ hA.eigenvalues k) {t : ℝ} (ht : 0 < t) :
    (A + (t : ℂ) • 1)⁻¹ = ((hA.eigenvectorUnitary : Matrix n n ℂ)) *
      diagonal (fun k => (((hA.eigenvalues k + t)⁻¹ : ℝ) : ℂ)) *
      ((hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [add_const_decomp hA t]
  have hne : ∀ k, ((hA.eigenvalues k + t : ℝ) : ℂ) ≠ 0 := by
    intro k
    have : (0 : ℝ) < hA.eigenvalues k + t := by
      have := hpos k
      linarith
    exact_mod_cast this.ne'
  calc ((hA.eigenvectorUnitary : Matrix n n ℂ)) *
        diagonal (fun k => ((hA.eigenvalues k + t : ℝ) : ℂ)) *
        ((hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ *
        (((hA.eigenvectorUnitary : Matrix n n ℂ)) *
        diagonal (fun k => (((hA.eigenvalues k + t)⁻¹ : ℝ) : ℂ)) *
        ((hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ)
      = ((hA.eigenvectorUnitary : Matrix n n ℂ)) *
        (diagonal (fun k => ((hA.eigenvalues k + t : ℝ) : ℂ)) *
          (((hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ *
            ((hA.eigenvectorUnitary : Matrix n n ℂ))) *
          diagonal (fun k => (((hA.eigenvalues k + t)⁻¹ : ℝ) : ℂ))) *
        ((hA.eigenvectorUnitary : Matrix n n ℂ))ᴴ := by
          simp only [Matrix.mul_assoc]
    _ = 1 := by
          rw [eigen_unitary' hA, Matrix.mul_one, diagonal_mul_diagonal]
          rw [show (fun k => ((hA.eigenvalues k + t : ℝ) : ℂ) *
              (((hA.eigenvalues k + t)⁻¹ : ℝ) : ℂ)) = fun _ : n => (1 : ℂ) from by
            funext k
            rw [← Complex.ofReal_mul, mul_inv_cancel₀]
            · simp
            · exact_mod_cast (by simpa using hne k : ((hA.eigenvalues k + t : ℝ) : ℂ) ≠ 0)]
          rw [show diagonal (fun _ : n => (1 : ℂ)) = 1 from by simp, Matrix.mul_one,
            eigen_unitary hA]

/-- The quadratic form of the resolvent. -/
