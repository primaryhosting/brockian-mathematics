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

lemma fidelity_self {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) : fidelity ρ ρ = ρ.trace.re := by
  have hsq : CFC.sqrt ρ * ρ * CFC.sqrt ρ = ρ ^ 2 := by
    conv_lhs => rw [← CFC.sqrt_mul_sqrt_self ρ hρ.nonneg]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self ρ hρ.nonneg,
      ← Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self ρ hρ.nonneg, sq]
  rw [fidelity, hsq, CFC.sqrt_sq ρ hρ.nonneg]

/-- **Uhlmann's theorem**: the fidelity of two positive semidefinite matrices `ρ`, `σ` is the
maximum of the overlap `|⟪ψ, φ⟫|` taken over all purifications `ψ` of `ρ` and `φ` of `σ`
(with an ancilla of the same dimension). -/
