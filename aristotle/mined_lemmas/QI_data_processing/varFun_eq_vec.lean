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

lemma varFun_eq_vec {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (t : ℝ) (Z : Matrix n n ℂ) :
    varFun ρ σ t Z
      = 2 * (star (vecm (Z * CFC.sqrt ρ)) ⬝ᵥ vecm (CFC.sqrt ρ)).re
        - (star (vecm (Z * CFC.sqrt ρ)) ⬝ᵥ
            ((modOp σ ρ + (t : ℂ) • 1) *ᵥ vecm (Z * CFC.sqrt ρ))).re := by
  set s := CFC.sqrt ρ with hs
  have hsH : sᴴ = s := sqrt_herm hρ
  have hss : s * s = ρ := sqrt_mul_sqrt hρ
  have hsis : s * ρ⁻¹ * s = 1 := sqrt_mul_inv_mul_sqrt hρ
  have e1 : star (vecm (Z * s)) ⬝ᵥ vecm s = trace (Zᴴ * ρ) := by
    rw [dot_vecm, Matrix.conjTranspose_mul, hsH, Matrix.mul_assoc, Matrix.trace_mul_comm,
      Matrix.mul_assoc, hss]
  have e2 : (modOp σ ρ + (t : ℂ) • 1) *ᵥ vecm (Z * s)
      = vecm (σ * (Z * s) * ρ⁻¹) + (t : ℂ) • vecm (Z * s) := by
    rw [Matrix.add_mulVec, modOp_mulVec]
    congr 1
    simp [Matrix.smul_mulVec]
  have e3 : star (vecm (Z * s)) ⬝ᵥ vecm (σ * (Z * s) * ρ⁻¹) = trace (Zᴴ * σ * Z) := by
    rw [dot_vecm, Matrix.conjTranspose_mul, hsH]
    calc trace (s * Zᴴ * (σ * (Z * s) * ρ⁻¹))
        = trace ((Zᴴ * σ * Z) * (s * ρ⁻¹ * s)) := by
          simp only [Matrix.mul_assoc]
          rw [Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
      _ = trace (Zᴴ * σ * Z) := by rw [hsis, Matrix.mul_one]
  have e4 : star (vecm (Z * s)) ⬝ᵥ vecm (Z * s) = trace (Zᴴ * Z * ρ) := by
    rw [dot_vecm, Matrix.conjTranspose_mul, hsH]
    calc trace (s * Zᴴ * (Z * s))
        = trace ((Zᴴ * Z) * (s * s)) := by
          simp only [Matrix.mul_assoc]
          rw [Matrix.trace_mul_comm]
          simp only [Matrix.mul_assoc]
      _ = trace (Zᴴ * Z * ρ) := by rw [hss]
  rw [e2, dotProduct_add, e1, e3, varFun]
  rw [show star (vecm (Z * s)) ⬝ᵥ ((t : ℂ) • vecm (Z * s))
      = (t : ℂ) * (star (vecm (Z * s)) ⬝ᵥ vecm (Z * s)) by
    rw [dotProduct_smul]; simp [smul_eq_mul]]
  rw [e4]
  simp
  ring

/-- The variational upper bound. -/
