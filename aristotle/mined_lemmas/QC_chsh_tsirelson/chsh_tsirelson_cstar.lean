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
