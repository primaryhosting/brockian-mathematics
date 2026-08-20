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

lemma dot_vecm (X Y : Matrix n m ℂ) : star (vecm X) ⬝ᵥ vecm Y = trace (Xᴴ * Y) := by
  simp [vecm, dotProduct, Matrix.trace, Matrix.mul_apply, Fintype.sum_prod_type, diag]
  rw [Finset.sum_comm]

omit [DecidableEq n] [DecidableEq m] in
/-- Action of a Kronecker product on a vectorized matrix. -/
