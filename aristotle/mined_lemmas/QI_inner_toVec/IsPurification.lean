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

def IsPurification (ψ : EuclideanSpace ℂ (n × m)) (ρ : Matrix n n ℂ) : Prop := reduced ψ = ρ

omit [Fintype n] in
