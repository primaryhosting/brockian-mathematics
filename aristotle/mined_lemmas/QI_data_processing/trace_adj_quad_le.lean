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

lemma trace_adj_quad_le (hK : ∑ i, (K i)ᴴ * K i = 1) (Z : Matrix m m ℂ)
    {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    (trace ((krausAdj K Z)ᴴ * σ * (krausAdj K Z))).re
      ≤ (trace (Zᴴ * krausMap K σ * Z)).re := by
  set W := krausAdj K Z with hW
  have hks := kadison_schwarz K hK Zᴴ
  rw [Matrix.conjTranspose_conjTranspose] at hks
  have h1 : (trace (Wᴴ * σ * W)).re = (trace ((krausAdj K Z * krausAdj K Zᴴ) * σ)).re := by
    rw [Matrix.trace_mul_cycle, hW, krausAdj_conjTranspose]
  have h2 : (trace (Zᴴ * krausMap K σ * Z)).re
      = (trace (krausAdj K (Z * Zᴴ) * σ)).re := by
    rw [trace_krausAdj_mul, Matrix.trace_mul_cycle]
  rw [h1, h2, ← sub_nonneg, ← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.sub_mul]
  exact trace_mul_nonneg hks hσ

/-- Contractivity of the adjoint in the `ρ`-weighted norm. -/
