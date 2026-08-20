import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# The Robertson uncertainty relation

For two observables (bounded self-adjoint operators) `A`, `B` on a complex Hilbert space `H`
and a state `ψ`, the standard deviations satisfy

  `ΔA · ΔB ≥ ½ |⟨[A, B]⟩|`.

Here `⟨X⟩ = ⟪ψ, X ψ⟫` is the expectation value, `ΔA = ‖(A - ⟨A⟩) ψ‖`, and `[A, B] = AB - BA`.
The theorem `QC.stdDev_sq` confirms that for a unit vector `ψ` and a self-adjoint `A`,
`(ΔA)² = ⟨A²⟩ - ⟨A⟩²`, so `stdDev` is indeed the usual standard deviation.
-/

namespace QC

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The expectation value `⟨A⟩ = ⟪ψ, A ψ⟫` of an operator `A` in the state `ψ`. -/

lemma commutator_shift (A B : H →L[ℂ] H) (a b : ℂ) :
    commutator (A - a • (1 : H →L[ℂ] H)) (B - b • (1 : H →L[ℂ] H)) = commutator A B := by
  simp only [commutator, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_sub, smul_smul, mul_comm a b]
  abel

/-- **Robertson's uncertainty relation**: for observables (self-adjoint operators) `A`, `B`
and a state `ψ`, `ΔA · ΔB ≥ ½ |⟨[A, B]⟩|`. -/
