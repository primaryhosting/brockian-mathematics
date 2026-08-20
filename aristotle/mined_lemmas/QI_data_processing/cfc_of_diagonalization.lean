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

theorem cfc_of_diagonalization {A U : Matrix n n ℂ} (hU : U ∈ unitary (Matrix n n ℂ))
    (d : n → ℝ) (hA : A = U * diagonal (fun i => ((d i : ℝ) : ℂ)) * Uᴴ) (f : ℝ → ℝ) :
    cfc f A = U * diagonal (fun i => ((f (d i) : ℝ) : ℂ)) * Uᴴ := by
  have hherm : (diagonal (fun i => ((d i : ℝ) : ℂ))).IsHermitian := by
    rw [Matrix.IsHermitian, diagonal_conjTranspose]
    simp [Pi.star_def]
  rw [hA, cfc_unitary_conj hU hherm f, cfc_diagonal]

/-- The quadratic form of a matrix conjugate to a diagonal one. -/
