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

theorem varFun_channel_le (hK : ∑ i, (K i)ᴴ * K i = 1) {ρ σ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {t : ℝ} (ht : 0 ≤ t) (Z : Matrix m m ℂ) :
    varFun (krausMap K ρ) (krausMap K σ) t Z ≤ varFun ρ σ t (krausAdj K Z) := by
  have h1 : (trace (Zᴴ * krausMap K ρ)).re = (trace ((krausAdj K Z)ᴴ * ρ)).re := by
    rw [trace_adj_id]
  have h2 := trace_adj_quad_le hK Z hσ
  have h3 := trace_adj_sq_le hK Z hρ
  rw [varFun, varFun, h1]
  have h3' : t * (trace ((krausAdj K Z)ᴴ * krausAdj K Z * ρ)).re
      ≤ t * (trace (Zᴴ * Z * krausMap K ρ)).re := mul_le_mul_of_nonneg_left h3 ht
  linarith

/-- The resolvent quadratic form decreases along the channel. -/
