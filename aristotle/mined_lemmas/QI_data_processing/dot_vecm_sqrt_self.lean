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

lemma dot_vecm_sqrt_self {ρ : Matrix n n ℂ} (hρ : ρ.PosDef) :
    star (vecm (CFC.sqrt ρ)) ⬝ᵥ vecm (CFC.sqrt ρ) = trace ρ := by
  rw [dot_vecm, sqrt_herm hρ, sqrt_mul_sqrt hρ]

/-- Integral formula for the relative entropy. -/
