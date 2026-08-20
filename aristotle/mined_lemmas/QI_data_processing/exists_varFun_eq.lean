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

theorem exists_varFun_eq {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) {t : ℝ}
    (ht : 0 < t) : ∃ Z : Matrix n n ℂ, resolvQuad ρ σ t = varFun ρ σ t Z := by
  set s := CFC.sqrt ρ with hs
  have hsd : s.PosDef := sqrt_posDef hρ
  set S := modOp σ ρ + (t : ℂ) • 1 with hS
  have hSpd : S.PosDef := shifted_modOp_posDef hρ hσ ht
  refine ⟨unvecm (S⁻¹ *ᵥ vecm s) * s⁻¹, ?_⟩
  have hZs : (unvecm (S⁻¹ *ᵥ vecm s) * s⁻¹) * s = unvecm (S⁻¹ *ᵥ vecm s) := by
    rw [Matrix.mul_assoc, posDef_inv_mul hsd, Matrix.mul_one]
  rw [varFun_eq_vec hρ t, hZs, vecm_unvecm, resolvQuad, ← hs, ← hS]
  exact (variational_eq hSpd (vecm s)).symm

/-! ### Behaviour under a channel -/

variable {K : ι → Matrix m n ℂ}

/-- The variational functional decreases along the channel. -/
