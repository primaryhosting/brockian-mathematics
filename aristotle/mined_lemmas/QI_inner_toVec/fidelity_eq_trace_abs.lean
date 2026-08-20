import Mathlib

/-!
# Uhlmann's theorem

For positive semidefinite matrices `ρ σ : Matrix n n ℂ` (density operators, not necessarily
normalized), the fidelity

`F(ρ, σ) = Tr √(√ρ σ √ρ)`

equals the maximum of `|⟪ψ, φ⟫|` over all purifications `ψ` of `ρ` and `φ` of `σ` in
`ℂⁿ ⊗ ℂⁿ ≃ EuclideanSpace ℂ (n × n)`, where the reduced density matrix of a vector `ψ` is
the partial trace over the second tensor factor.

The main result is `QI.uhlmann_fidelity`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Matrix
open scoped ComplexOrder InnerProductSpace MatrixOrder

namespace QI

variable {n m : Type*} [Fintype n] [Fintype m]

/-! ### Vectorization of matrices -/

/-- The vectorization of a matrix, viewed as a vector of the Hilbert space
`EuclideanSpace ℂ (n × m) ≃ ℂⁿ ⊗ ℂᵐ`. -/

lemma fidelity_eq_trace_abs (ρ : Matrix n n ℂ) {σ : Matrix n n ℂ} (hσ : σ.PosSemidef) :
    fidelity ρ σ = (CFC.abs (CFC.sqrt σ * CFC.sqrt ρ)).trace.re := by
  rw [fidelity]
  congr 2
  rw [CFC.abs, star_eq_conjTranspose, Matrix.conjTranspose_mul,
    (CFC.sqrt_nonneg ρ).posSemidef.isHermitian, (CFC.sqrt_nonneg σ).posSemidef.isHermitian]
  congr 1
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt σ),
    CFC.sqrt_mul_sqrt_self σ hσ.nonneg]

/-- Sanity check: the fidelity of a state with itself is its trace. -/
