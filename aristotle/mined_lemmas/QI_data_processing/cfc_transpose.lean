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

lemma cfc_transpose {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f Aᵀ = (cfc f A)ᵀ := by
  obtain ⟨U, d, hU, hU', hdec⟩ := exists_diagonalization hA
  have hVH : (Uᴴᵀ)ᴴ = Uᵀ := by ext i j; simp [Matrix.conjTranspose_apply]
  have hV1 : Uᴴᵀ * (Uᴴᵀ)ᴴ = 1 := by
    rw [hVH, ← Matrix.transpose_mul, hU, Matrix.transpose_one]
  have hV2 : (Uᴴᵀ)ᴴ * Uᴴᵀ = 1 := by
    rw [hVH, ← Matrix.transpose_mul, hU', Matrix.transpose_one]
  have hdiagT : ∀ g : ℝ → ℝ, (diagonal (fun i => ((g (d i) : ℝ) : ℂ)))ᵀ
      = diagonal (fun i => ((g (d i) : ℝ) : ℂ)) := by
    intro g
    ext i j
    by_cases h : i = j <;> simp [h, eq_comm]
  have hdiagT0 : (diagonal (fun i => ((d i : ℝ) : ℂ)))ᵀ = diagonal (fun i => ((d i : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j <;> simp [h, eq_comm]
  have hdecT : Aᵀ = Uᴴᵀ * diagonal (fun i => ((d i : ℝ) : ℂ)) * (Uᴴᵀ)ᴴ := by
    conv_lhs => rw [hdec]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hVH, hdiagT0, Matrix.mul_assoc]
  rw [cfc_of_diagonalization (unitary_of_mul hV1 hV2) d hdecT f,
    cfc_of_diagonalization (unitary_of_mul hU hU') d hdec f,
    Matrix.transpose_mul, Matrix.transpose_mul, hVH, hdiagT f, Matrix.mul_assoc]

/-- The logarithm of a Kronecker product of positive definite matrices. -/
