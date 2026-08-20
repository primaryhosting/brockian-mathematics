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

theorem relEntropy_eq_neg_integral {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    relEntropy ρ σ
      = - ∫ t in Set.Ioi (0:ℝ), resolvIntegrand (modOp σ ρ) (vecm (CFC.sqrt ρ)) t := by
  have hpd := modOp_posDef hσ hρ
  rw [relEntropy_eq_quadForm hρ hσ,
    quadForm_log_eq_integral hpd.isHermitian hpd.eigenvalues_pos]

/-! ### The variational characterization of resolvent quadratic forms -/

