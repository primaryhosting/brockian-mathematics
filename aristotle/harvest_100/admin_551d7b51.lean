/-
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

section Algebraic

variable {R : Type*} [Ring R]

/-- The CHSH operator associated to four observables. -/
def chshOp (A₀ A₁ B₀ B₁ : R) : R := A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁

/-- The square of the CHSH operator built from a CHSH tuple equals
`4 - [A₀, A₁] * [B₀, B₁]`. -/
theorem chshOp_sq {A₀ A₁ B₀ B₁ : R} [StarMul R] (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    chshOp A₀ A₁ B₀ B₁ ^ 2
      = 4 - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀) := by
  have a0 : A₀ * A₀ = 1 := by rw [← sq]; exact T.A₀_inv
  have a1 : A₁ * A₁ = 1 := by rw [← sq]; exact T.A₁_inv
  have b0 : B₀ * B₀ = 1 := by rw [← sq]; exact T.B₀_inv
  have b1 : B₁ * B₁ = 1 := by rw [← sq]; exact T.B₁_inv
  have d00 : ∀ x : R, B₀ * (A₀ * x) = A₀ * (B₀ * x) := fun x => by
    rw [← mul_assoc, ← T.A₀B₀_commutes, mul_assoc]
  have d01 : ∀ x : R, B₁ * (A₀ * x) = A₀ * (B₁ * x) := fun x => by
    rw [← mul_assoc, ← T.A₀B₁_commutes, mul_assoc]
  have d10 : ∀ x : R, B₀ * (A₁ * x) = A₁ * (B₀ * x) := fun x => by
    rw [← mul_assoc, ← T.A₁B₀_commutes, mul_assoc]
  have d11 : ∀ x : R, B₁ * (A₁ * x) = A₁ * (B₁ * x) := fun x => by
    rw [← mul_assoc, ← T.A₁B₁_commutes, mul_assoc]
  have e0 : ∀ x : R, A₀ * (A₀ * x) = x := fun x => by rw [← mul_assoc, a0, one_mul]
  have e1 : ∀ x : R, A₁ * (A₁ * x) = x := fun x => by rw [← mul_assoc, a1, one_mul]
  simp only [chshOp, sq, add_mul, mul_add, sub_mul, mul_sub, mul_assoc, d00, d01, d10, d11,
    e0, e1, a0, a1, b0, b1, mul_one]
  noncomm_ring
  simp
  abel

/-- The CHSH operator of a CHSH tuple is self-adjoint. -/
theorem isSelfAdjoint_chshOp [StarRing R] {A₀ A₁ B₀ B₁ : R} (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    star (chshOp A₀ A₁ B₀ B₁) = chshOp A₀ A₁ B₀ B₁ := by
  simp only [chshOp, star_sub, star_add, star_mul, T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa,
    ← T.A₀B₀_commutes, ← T.A₀B₁_commutes, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]

end Algebraic

section CStar

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]

/-- In a unital C*-ring, the unit has norm at most `1` (it is `0` only in the trivial ring). -/
theorem norm_one_le_one : ‖(1 : A)‖ ≤ 1 := by
  have h : ‖(1 : A)‖ * ‖(1 : A)‖ = ‖(1 : A)‖ := by
    have := CStarRing.norm_star_mul_self (x := (1 : A))
    simpa [sq] using this.symm
  nlinarith [norm_nonneg (1 : A)]

/-- A self-adjoint involution in a C*-ring has norm at most `1`. -/
theorem norm_le_one_of_sa_involution {a : A} (hsq : a ^ 2 = 1) (hsa : star a = a) : ‖a‖ ≤ 1 := by
  have h : ‖a‖ * ‖a‖ = ‖(1 : A)‖ := by
    have := CStarRing.norm_star_mul_self (x := a)
    rw [hsa] at this
    have ha : a * a = (1 : A) := by rw [← sq]; exact hsq
    rw [ha] at this
    rw [this]
  nlinarith [norm_nonneg a, norm_one_le_one (A := A)]

/-- The commutator of two self-adjoint involutions has norm at most `2`. -/
theorem norm_commutator_le_two {a b : A} (ha : a ^ 2 = 1) (ha' : star a = a)
    (hb : b ^ 2 = 1) (hb' : star b = b) : ‖a * b - b * a‖ ≤ 2 := by
  have h1 : ‖a‖ ≤ 1 := norm_le_one_of_sa_involution ha ha'
  have h2 : ‖b‖ ≤ 1 := norm_le_one_of_sa_involution hb hb'
  have hab : ‖a * b‖ ≤ 1 := by
    calc ‖a * b‖ ≤ ‖a‖ * ‖b‖ := norm_mul_le _ _
      _ ≤ 1 := by nlinarith [norm_nonneg a, norm_nonneg b]
  have hba : ‖b * a‖ ≤ 1 := by
    calc ‖b * a‖ ≤ ‖b‖ * ‖a‖ := norm_mul_le _ _
      _ ≤ 1 := by nlinarith [norm_nonneg a, norm_nonneg b]
  calc ‖a * b - b * a‖ ≤ ‖a * b‖ + ‖b * a‖ := norm_sub_le _ _
    _ ≤ 2 := by linarith

/-- **Tsirelson's bound.** In any unital C*-algebra (in particular for bounded operators on a
Hilbert space), the CHSH operator `A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁` built from a CHSH tuple has
norm at most `2√2`. -/
theorem chsh_tsirelson (A₀ A₁ B₀ B₁ : A) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ ≤ 2 * Real.sqrt 2 := by
  set S : A := chshOp A₀ A₁ B₀ B₁ with hS
  have hsa : star S = S := isSelfAdjoint_chshOp T
  have hnormsq : ‖S‖ * ‖S‖ = ‖S ^ 2‖ := by
    have := CStarRing.norm_star_mul_self (x := S)
    rw [hsa] at this
    rw [sq, ← this]
  have hsq : S ^ 2 = 4 - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀) := chshOp_sq T
  have hCA : ‖A₀ * A₁ - A₁ * A₀‖ ≤ 2 :=
    norm_commutator_le_two T.A₀_inv T.A₀_sa T.A₁_inv T.A₁_sa
  have hCB : ‖B₀ * B₁ - B₁ * B₀‖ ≤ 2 :=
    norm_commutator_le_two T.B₀_inv T.B₀_sa T.B₁_inv T.B₁_sa
  have hfour : ‖(4 : A)‖ ≤ 4 := by
    have h : ((4 : ℕ) : A) = (4 : A) := by norm_num
    have h4 := Nat.norm_cast_le (α := A) 4
    rw [h] at h4
    have h1 : ‖(1 : A)‖ ≤ 1 := norm_one_le_one
    simp only [Nat.cast_ofNat] at h4
    nlinarith [norm_nonneg (1 : A)]
  have hprod : ‖(A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀)‖ ≤ 4 := by
    calc ‖(A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀)‖
        ≤ ‖A₀ * A₁ - A₁ * A₀‖ * ‖B₀ * B₁ - B₁ * B₀‖ := norm_mul_le _ _
      _ ≤ 4 := by nlinarith [norm_nonneg (A₀ * A₁ - A₁ * A₀), norm_nonneg (B₀ * B₁ - B₁ * B₀)]
  have h8 : ‖S‖ * ‖S‖ ≤ 8 := by
    rw [hnormsq, hsq]
    calc ‖(4 : A) - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀)‖
        ≤ ‖(4 : A)‖ + ‖(A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀)‖ := norm_sub_le _ _
      _ ≤ 8 := by linarith
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have : ‖S‖ ≤ 2 * Real.sqrt 2 := by nlinarith [norm_nonneg S]
  simpa [hS, chshOp] using this

end CStar

section Operators

/-- **Tsirelson's bound for operators on a Hilbert space.** If `A₀, A₁, B₀, B₁` are bounded
operators on a complex Hilbert space forming a CHSH tuple (self-adjoint involutions, with the
`Aᵢ` commuting with the `Bⱼ`), then the CHSH operator has operator norm at most `2√2`. -/
theorem chsh_tsirelson_operator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A₀ A₁ B₀ B₁ : H →L[ℂ] H) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ ≤ 2 * Real.sqrt 2 :=
  chsh_tsirelson A₀ A₁ B₀ B₁ T

end Operators

end QC

