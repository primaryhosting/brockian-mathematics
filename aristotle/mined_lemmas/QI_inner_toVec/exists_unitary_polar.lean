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

theorem exists_unitary_polar (M : Matrix n n ℂ) :
    ∃ W : Matrix n n ℂ, W ∈ unitary (Matrix n n ℂ) ∧ M = W * CFC.abs M := by
  have habs : (CFC.abs M).PosSemidef := (CFC.abs_nonneg M).posSemidef
  obtain ⟨U, hUu, hU⟩ := exists_unitary_of_mul_conjTranspose_eq (X := Mᴴ) (Y := CFC.abs M) (by
    rw [Matrix.conjTranspose_conjTranspose, habs.isHermitian, CFC.abs_mul_abs,
      star_eq_conjTranspose])
  refine ⟨Uᴴ, Unitary.star_mem hUu, ?_⟩
  conv_lhs => rw [← Matrix.conjTranspose_conjTranspose M, hU]
  rw [Matrix.conjTranspose_mul, habs.isHermitian]

/-! ### The trace bound -/

