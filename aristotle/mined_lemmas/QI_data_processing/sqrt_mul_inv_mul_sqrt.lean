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

lemma sqrt_mul_inv_mul_sqrt {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) :
    CFC.sqrt ρ * ρ⁻¹ * CFC.sqrt ρ = 1 := by
  set s := CFC.sqrt ρ with hs
  have hsd : s.PosDef := sqrt_posDef hρ
  have hss : s * s = ρ := sqrt_mul_sqrt hρ
  rw [← hss, Matrix.mul_inv_rev,
    show s * (s⁻¹ * s⁻¹) * s = (s * s⁻¹) * (s⁻¹ * s) by simp [Matrix.mul_assoc],
    posDef_mul_inv hsd, posDef_inv_mul hsd, Matrix.one_mul]

/-- The variational functional in vectorized form. -/
