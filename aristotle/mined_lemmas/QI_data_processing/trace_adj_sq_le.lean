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

lemma trace_adj_sq_le (hK : ∑ i, (K i)ᴴ * K i = 1) (Z : Matrix m m ℂ)
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (trace ((krausAdj K Z)ᴴ * (krausAdj K Z) * ρ)).re
      ≤ (trace (Zᴴ * Z * krausMap K ρ)).re := by
  have hks := kadison_schwarz K hK Z
  have h1 : (trace ((krausAdj K Z)ᴴ * (krausAdj K Z) * ρ)).re
      = (trace ((krausAdj K Zᴴ * krausAdj K Z) * ρ)).re := by
    rw [krausAdj_conjTranspose]
  have h2 : (trace (Zᴴ * Z * krausMap K ρ)).re
      = (trace (krausAdj K (Zᴴ * Z) * ρ)).re := by
    rw [trace_krausAdj_mul]
  rw [h1, h2, ← sub_nonneg, ← Complex.sub_re, ← Matrix.trace_sub, ← Matrix.sub_mul]
  exact trace_mul_nonneg hks hρ

end QI

