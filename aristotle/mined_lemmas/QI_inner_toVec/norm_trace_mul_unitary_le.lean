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

lemma norm_trace_mul_unitary_le (M : Matrix n n ℂ) {W : Matrix n n ℂ}
    (hW : W ∈ unitary (Matrix n n ℂ)) : ‖(M * W).trace‖ ≤ (CFC.abs M).trace.re := by
  obtain ⟨W₀, hW₀u, hW₀⟩ := exists_unitary_polar M
  have key : (M * W).trace = (CFC.abs M * (W * W₀)).trace := by
    conv_lhs => rw [hW₀]
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
  rw [key]
  exact norm_trace_posSemidef_mul_unitary_le (posSemidef_abs M) (mul_mem hW hW₀u)

/-! ### Fidelity -/

/-- The fidelity `F(ρ, σ) = Tr √(√ρ σ √ρ)` of two positive semidefinite matrices. -/
