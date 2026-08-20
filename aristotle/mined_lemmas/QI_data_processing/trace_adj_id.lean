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

lemma trace_adj_id (K : ι → Matrix m n ℂ) (Z : Matrix m m ℂ) (ρ : Matrix n n ℂ) :
    trace ((krausAdj K Z)ᴴ * ρ) = trace (Zᴴ * krausMap K ρ) := by
  rw [krausAdj_conjTranspose, trace_krausAdj_mul]

/-- Contractivity of the adjoint in the `σ`-weighted norm. -/
