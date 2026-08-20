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

theorem relEntropy_eq_quadForm {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    relEntropy ρ σ
      = -(star (vecm (CFC.sqrt ρ)) ⬝ᵥ
            ((cfc Real.log (modOp σ ρ)) *ᵥ vecm (CFC.sqrt ρ))).re := by
  have hlog : cfc Real.log (modOp σ ρ)
      = (cfc Real.log σ) ⊗ₖ (1 : Matrix n n ℂ)
        + (1 : Matrix n n ℂ) ⊗ₖ (- (cfc Real.log ρ))ᵀ := by
    rw [modOp, cfc_log_kron hσ (hρ.inv.transpose), cfc_transpose hρ.inv.isHermitian,
      cfc_log_inv hρ]
  rw [hlog]
  set s := CFC.sqrt ρ with hs
  have hss : s * s = ρ := sqrt_mul_sqrt hρ
  have hsH : sᴴ = s := sqrt_herm hρ
  have h1 : ((cfc Real.log σ) ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ vecm s
      = vecm ((cfc Real.log σ) * s * 1) := by
    have := kron_mulVecm (cfc Real.log σ) (1 : Matrix n n ℂ) s
    rwa [Matrix.transpose_one] at this
  have h2 : ((1 : Matrix n n ℂ) ⊗ₖ (- (cfc Real.log ρ))ᵀ) *ᵥ vecm s
      = vecm (1 * s * (- cfc Real.log ρ)) := kron_mulVecm _ _ _
  rw [Matrix.add_mulVec, h1, h2, dotProduct_add, Complex.add_re, dot_vecm, dot_vecm]
  rw [Matrix.mul_one, Matrix.one_mul, hsH]
  have e1 : trace (s * ((cfc Real.log σ) * s)) = trace (ρ * cfc Real.log σ) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hss,
      Matrix.trace_mul_comm]
  have e2 : trace (s * (s * (- cfc Real.log ρ))) = - trace (ρ * cfc Real.log ρ) := by
    rw [← Matrix.mul_assoc, hss, Matrix.mul_neg, Matrix.trace_neg]
  rw [e1, e2, relEntropy]
  simp
  ring

/-- The squared norm of `vecm √ρ` is the trace of `ρ`. -/
