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

lemma trace_krausAdj_mul (K : ι → Matrix m n ℂ) (Z : Matrix m m ℂ) (X : Matrix n n ℂ) :
    trace (krausAdj K Z * X) = trace (Z * krausMap K X) := by
  simp only [krausAdj, krausMap, Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (K i)ᴴ * Z * K i * X = (K i)ᴴ * (Z * K i * X) by simp [Matrix.mul_assoc],
    Matrix.trace_mul_comm]
  simp [Matrix.mul_assoc]

omit [DecidableEq ι] in
/-- Trace preservation. -/
