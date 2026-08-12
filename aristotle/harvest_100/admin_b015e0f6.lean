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
noncomputable def expect (A : H →L[ℂ] H) (psi : H) : ℂ := ⟪psi, A psi⟫_ℂ

/-- The standard deviation `ΔA = ‖(A - ⟨A⟩) ψ‖` of an observable `A` in the state `ψ`. -/
noncomputable def stdDev (A : H →L[ℂ] H) (psi : H) : ℝ :=
  ‖(A - expect A psi • (1 : H →L[ℂ] H)) psi‖

/-- The commutator `[A, B] = A B - B A`. -/
noncomputable def commutator (A B : H →L[ℂ] H) : H →L[ℂ] H := A * B - B * A

/-- A self-adjoint operator can be moved across the inner product. -/
lemma inner_selfAdjoint_move {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (x y : H) :
    ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ := by
  conv_lhs => rw [← hA.star_eq]
  simp [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- The expectation value of a self-adjoint operator is real. -/
lemma conj_expect (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (psi : H) :
    (starRingEnd ℂ) (expect A psi) = expect A psi := by
  rw [expect, inner_conj_symm, inner_selfAdjoint_move hA]

/-- Shifting a self-adjoint operator by its (real) expectation value keeps it self-adjoint. -/
lemma isSelfAdjoint_shift (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (psi : H) :
    IsSelfAdjoint (A - expect A psi • (1 : H →L[ℂ] H)) := by
  have h := conj_expect A hA psi
  simpa [IsSelfAdjoint, star_smul, h] using hA.star_eq

omit [CompleteSpace H] in
/-- The commutator is unchanged when each argument is shifted by a scalar. -/
lemma commutator_shift (A B : H →L[ℂ] H) (a b : ℂ) :
    commutator (A - a • (1 : H →L[ℂ] H)) (B - b • (1 : H →L[ℂ] H)) = commutator A B := by
  simp only [commutator, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_sub, smul_smul, mul_comm a b]
  abel

/-- **Robertson's uncertainty relation**: for observables (self-adjoint operators) `A`, `B`
and a state `ψ`, `ΔA · ΔB ≥ ½ |⟨[A, B]⟩|`. -/
theorem robertson_uncertainty (A B : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (psi : H) :
    stdDev A psi * stdDev B psi ≥ (1 / 2) * ‖expect (commutator A B) psi‖ := by
  set A' : H →L[ℂ] H := A - expect A psi • (1 : H →L[ℂ] H) with hA'def
  set B' : H →L[ℂ] H := B - expect B psi • (1 : H →L[ℂ] H) with hB'def
  have hA' : IsSelfAdjoint A' := isSelfAdjoint_shift A hA psi
  have hB' : IsSelfAdjoint B' := isSelfAdjoint_shift B hB psi
  set z : ℂ := ⟪A' psi, B' psi⟫_ℂ with hz
  have key : expect (commutator A B) psi = z - (starRingEnd ℂ) z := by
    rw [← commutator_shift A B (expect A psi) (expect B psi), ← hA'def, ← hB'def]
    simp only [expect, commutator, ContinuousLinearMap.sub_apply, inner_sub_right,
      ContinuousLinearMap.mul_apply]
    rw [← inner_selfAdjoint_move hA' psi (B' psi), ← inner_selfAdjoint_move hB' psi (A' psi), hz,
      inner_conj_symm]
  rw [key, Complex.sub_conj]
  have h1 : ‖((2 * z.im : ℝ) : ℂ) * Complex.I‖ = 2 * |z.im| := by simp
  rw [h1]
  have h2 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have h3 : ‖z‖ ≤ stdDev A psi * stdDev B psi := norm_inner_le_norm _ _
  linarith

/-- For a unit vector `ψ` and a self-adjoint `A` we have `(ΔA)² = ⟨A²⟩ - ⟨A⟩²`, i.e. `stdDev`
is the standard deviation of the observable `A` in the state `ψ`. -/
theorem stdDev_sq (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (psi : H) (hpsi : ‖psi‖ = 1) :
    (stdDev A psi) ^ 2 = (expect (A * A) psi).re - ((expect A psi).re) ^ 2 := by
  set a : ℂ := expect A psi with ha
  have him : a.im = 0 := by
    have h := conj_expect A hA psi
    rw [← ha] at h
    have h' := congrArg Complex.im h
    simp [Complex.conj_im] at h'
    linarith
  have hnorm : ‖a‖ = |a.re| := by
    simp [Complex.norm_def, Complex.normSq_apply, him, ← Real.sqrt_sq_eq_abs, sq]
  have happ : (A - a • (1 : H →L[ℂ] H)) psi = A psi - a • psi := by simp
  rw [stdDev, ← ha, happ, norm_sub_sq (𝕜 := ℂ)]
  have h1 : ‖A psi‖ ^ 2 = (expect (A * A) psi).re := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_selfAdjoint_move hA]
    simp [expect]
  have h2 : ⟪A psi, a • psi⟫_ℂ = a * a := by
    rw [inner_smul_right, ← inner_conj_symm, ← expect, ← ha, conj_expect A hA psi, ← ha]
  have h3 : ‖a • psi‖ ^ 2 = a.re ^ 2 := by
    rw [norm_smul, hpsi, hnorm]
    simp [sq_abs]
  have h4 : RCLike.re (a * a) = a.re ^ 2 := by simp [him, sq]
  rw [h1, h2, h3, h4]
  ring

end QC

