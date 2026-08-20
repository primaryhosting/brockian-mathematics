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

lemma trace_krausMap (K : ι → Matrix m n ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1) (X : Matrix n n ℂ) :
    trace (krausMap K X) = trace X := by
  have h := trace_krausAdj_mul K (1 : Matrix m m ℂ) X
  rw [Matrix.one_mul] at h
  rw [← h]
  simp only [krausAdj, Matrix.mul_one]
  rw [hK, Matrix.one_mul]

omit [DecidableEq n] [DecidableEq m] [DecidableEq ι] in
/-- Positivity: a Kraus map sends positive semidefinite matrices to positive semidefinite
matrices. -/
