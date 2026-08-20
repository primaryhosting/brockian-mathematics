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

lemma norm_trace_posSemidef_mul_unitary_le {P U : Matrix n n ℂ} (hP : P.PosSemidef)
    (hU : U ∈ unitary (Matrix n n ℂ)) : ‖(P * U).trace‖ ≤ P.trace.re := by
  have hUU' : U * Uᴴ = 1 := by simpa [star_eq_conjTranspose] using (Unitary.mem_iff.mp hU).2
  set S : Matrix n n ℂ := CFC.sqrt P with hSdef
  have hS : S.PosSemidef := (CFC.sqrt_nonneg P).posSemidef
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P hP.nonneg
  have hSh : Sᴴ = S := hS.isHermitian
  have key : (P * U).trace = (Sᴴ * (S * U)).trace := by rw [hSh, ← Matrix.mul_assoc, hSS]
  have h1 : ‖toVec S‖ ^ 2 = P.trace.re := by rw [norm_toVec_sq, hSh, hSS]
  have h2 : ‖toVec (S * U)‖ ^ 2 = P.trace.re := by
    rw [norm_toVec_sq]
    congr 1
    rw [Matrix.conjTranspose_mul, hSh, Matrix.mul_assoc, ← Matrix.mul_assoc S S, hSS,
      Matrix.trace_mul_comm, Matrix.mul_assoc, hUU', Matrix.mul_one]
  have heq : ‖toVec S‖ = ‖toVec (S * U)‖ := by
    nlinarith [norm_nonneg (toVec S), norm_nonneg (toVec (S * U)), h1, h2]
  calc ‖(P * U).trace‖ = ‖(Sᴴ * (S * U)).trace‖ := by rw [key]
    _ ≤ ‖toVec S‖ * ‖toVec (S * U)‖ := norm_trace_conjTranspose_mul_le _ _
    _ = P.trace.re := by rw [← heq, ← sq, h1]

/-- For any square matrix `M` and unitary `W`, `|Tr (M W)| ≤ Tr |M|`. -/
