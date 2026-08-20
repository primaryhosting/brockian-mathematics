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

section CStar

variable {𝔄 : Type*} [NormedRing 𝔄] [StarRing 𝔄] [CStarRing 𝔄]

/-- In a C⋆-ring the unit has norm at most one (it is `0` or `1`). -/
theorem norm_one_le : ‖(1 : 𝔄)‖ ≤ 1 := by
  have h : ‖(1 : 𝔄)‖ * ‖(1 : 𝔄)‖ = ‖(1 : 𝔄)‖ := by
    have := CStarRing.norm_star_mul_self (x := (1 : 𝔄))
    simpa using this.symm
  nlinarith [norm_nonneg (1 : 𝔄)]

/-- A self-adjoint involution in a C⋆-ring has norm at most one. -/
theorem norm_le_one_of_sa_involution {X : 𝔄} (hsa : star X = X) (hsq : X * X = 1) :
    ‖X‖ ≤ 1 := by
  have h : ‖X‖ * ‖X‖ = ‖(1 : 𝔄)‖ := by
    rw [← CStarRing.norm_star_mul_self, hsa, hsq]
  nlinarith [norm_nonneg X, norm_one_le (𝔄 := 𝔄)]

/-- The norm of a commutator of two self-adjoint involutions is at most `2`. -/
theorem norm_commutator_le {X Y : 𝔄} (hX : star X = X) (hXsq : X * X = 1)
    (hY : star Y = Y) (hYsq : Y * Y = 1) : ‖X * Y - Y * X‖ ≤ 2 := by
  have hx := norm_le_one_of_sa_involution hX hXsq
  have hy := norm_le_one_of_sa_involution hY hYsq
  have h1 : ‖X * Y‖ ≤ 1 := le_trans (norm_mul_le _ _) (by nlinarith [norm_nonneg X, norm_nonneg Y])
  have h2 : ‖Y * X‖ ≤ 1 := le_trans (norm_mul_le _ _) (by nlinarith [norm_nonneg X, norm_nonneg Y])
  calc ‖X * Y - Y * X‖ ≤ ‖X * Y‖ + ‖Y * X‖ := norm_sub_le _ _
    _ ≤ 2 := by linarith

/-- The square of the CHSH operator: `C ^ 2 = 4 - [A₀, A₁] [B₀, B₁]`. -/
theorem chsh_sq {𝔅 : Type*} [Ring 𝔅] [StarRing 𝔅] {A₀ A₁ B₀ B₁ : 𝔅}
    (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) * (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) =
      4 - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀) := by
  have hA₀ : A₀ * A₀ = 1 := by have := T.A₀_inv; rwa [sq] at this
  have hA₁ : A₁ * A₁ = 1 := by have := T.A₁_inv; rwa [sq] at this
  have hB₀ : B₀ * B₀ = 1 := by have := T.B₀_inv; rwa [sq] at this
  have hB₁ : B₁ * B₁ = 1 := by have := T.B₁_inv; rwa [sq] at this
  have c00 : ∀ x : 𝔅, B₀ * (A₀ * x) = A₀ * (B₀ * x) := by
    intro x; rw [← mul_assoc, ← T.A₀B₀_commutes, mul_assoc]
  have c01 : ∀ x : 𝔅, B₁ * (A₀ * x) = A₀ * (B₁ * x) := by
    intro x; rw [← mul_assoc, ← T.A₀B₁_commutes, mul_assoc]
  have c10 : ∀ x : 𝔅, B₀ * (A₁ * x) = A₁ * (B₀ * x) := by
    intro x; rw [← mul_assoc, ← T.A₁B₀_commutes, mul_assoc]
  have c11 : ∀ x : 𝔅, B₁ * (A₁ * x) = A₁ * (B₁ * x) := by
    intro x; rw [← mul_assoc, ← T.A₁B₁_commutes, mul_assoc]
  have hA₀' : ∀ x : 𝔅, A₀ * (A₀ * x) = x := by intro x; rw [← mul_assoc, hA₀, one_mul]
  have hA₁' : ∀ x : 𝔅, A₁ * (A₁ * x) = x := by intro x; rw [← mul_assoc, hA₁, one_mul]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc,
    c00, c01, c10, c11, hA₀, hA₁, hB₀, hB₁, hA₀', hA₁', mul_one]
  noncomm_ring
  simp only [zsmul_eq_mul, mul_one]
  push_cast
  abel

/-- Tsirelson's bound in an arbitrary C⋆-algebra: the CHSH operator built from a CHSH tuple
has norm at most `2 √2`. -/
theorem chsh_tsirelson_cstar (A₀ A₁ B₀ B₁ : 𝔄) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ ≤ 2 * Real.sqrt 2 := by
  set C : 𝔄 := A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ with hC
  have hsa : star C = C := by
    simp only [hC, star_sub, star_add, star_mul, T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa,
      ← T.A₀B₀_commutes, ← T.A₀B₁_commutes, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]
  have hsq : C * C = 4 - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀) := chsh_sq T
  have hnormsq : ‖C‖ * ‖C‖ = ‖C * C‖ := by
    rw [← CStarRing.norm_star_mul_self, hsa]
  have h4 : ‖(4 : 𝔄)‖ ≤ 4 := by
    have : (4 : 𝔄) = 1 + 1 + 1 + 1 := by norm_num
    rw [this]
    have h1 : ‖(1 : 𝔄)‖ ≤ 1 := norm_one_le
    calc ‖(1 : 𝔄) + 1 + 1 + 1‖ ≤ ‖(1 : 𝔄) + 1 + 1‖ + ‖(1 : 𝔄)‖ := norm_add_le _ _
      _ ≤ (‖(1 : 𝔄) + 1‖ + ‖(1 : 𝔄)‖) + ‖(1 : 𝔄)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖(1 : 𝔄)‖ + ‖(1 : 𝔄)‖) + ‖(1 : 𝔄)‖) + ‖(1 : 𝔄)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ 4 := by linarith
  have hKA : ‖A₀ * A₁ - A₁ * A₀‖ ≤ 2 :=
    norm_commutator_le T.A₀_sa (by have := T.A₀_inv; rwa [sq] at this) T.A₁_sa
      (by have := T.A₁_inv; rwa [sq] at this)
  have hKB : ‖B₀ * B₁ - B₁ * B₀‖ ≤ 2 :=
    norm_commutator_le T.B₀_sa (by have := T.B₀_inv; rwa [sq] at this) T.B₁_sa
      (by have := T.B₁_inv; rwa [sq] at this)
  have hK : ‖(A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀)‖ ≤ 4 := by
    refine le_trans (norm_mul_le _ _) ?_
    nlinarith [norm_nonneg (A₀ * A₁ - A₁ * A₀), norm_nonneg (B₀ * B₁ - B₁ * B₀)]
  have hbound : ‖C‖ * ‖C‖ ≤ 8 := by
    rw [hnormsq, hsq]
    calc ‖(4 : 𝔄) - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀)‖
        ≤ ‖(4 : 𝔄)‖ + ‖(A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀)‖ := norm_sub_le _ _
      _ ≤ 8 := by linarith
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2, norm_nonneg C, hbound]

end CStar

/-- **Tsirelson's bound** for the CHSH operator on a complex Hilbert space:
if `A₀, A₁, B₀, B₁` are bounded self-adjoint involutions (Boolean observables) such that each
`Aᵢ` commutes with each `Bⱼ`, then the CHSH operator `A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁` has operator
norm at most `2√2`. -/
theorem chsh_tsirelson {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A₀ A₁ B₀ B₁ : H →L[ℂ] H) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ ≤ 2 * Real.sqrt 2 :=
  chsh_tsirelson_cstar A₀ A₁ B₀ B₁ T

end QC

