/-!
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Statement: The quantum CHSH operator has operator norm ≤ 2√2 (Tsirelson's bound).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace QC

variable {A : Type*}

/-- The CHSH operator associated to a tuple of observables
`A₀, A₁` (Alice) and `B₀, B₁` (Bob). -/
def chshOp [Mul A] [Add A] [Sub A] (A₀ A₁ B₀ B₁ : A) : A :=
  A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁

section Ring

variable [Ring A] [StarRing A] {A₀ A₁ B₀ B₁ : A}

/-- The square of the CHSH operator equals `4` minus the product of the two commutators. -/
theorem chshOp_mul_self (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    chshOp A₀ A₁ B₀ B₁ * chshOp A₀ A₁ B₀ B₁ =
      4 - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀) := by
  have sA₀ : A₀ * A₀ = 1 := by rw [← sq, T.A₀_inv]
  have sA₁ : A₁ * A₁ = 1 := by rw [← sq, T.A₁_inv]
  have sB₀ : B₀ * B₀ = 1 := by rw [← sq, T.B₀_inv]
  have sB₁ : B₁ * B₁ = 1 := by rw [← sq, T.B₁_inv]
  have hA₀ : ∀ x : A, A₀ * (A₀ * x) = x := by intro x; rw [← mul_assoc, sA₀, one_mul]
  have hA₁ : ∀ x : A, A₁ * (A₁ * x) = x := by intro x; rw [← mul_assoc, sA₁, one_mul]
  have d₀₀ : ∀ x : A, B₀ * (A₀ * x) = A₀ * (B₀ * x) := by
    intro x; rw [← mul_assoc, ← T.A₀B₀_commutes, mul_assoc]
  have d₀₁ : ∀ x : A, B₁ * (A₀ * x) = A₀ * (B₁ * x) := by
    intro x; rw [← mul_assoc, ← T.A₀B₁_commutes, mul_assoc]
  have d₁₀ : ∀ x : A, B₀ * (A₁ * x) = A₁ * (B₀ * x) := by
    intro x; rw [← mul_assoc, ← T.A₁B₀_commutes, mul_assoc]
  have d₁₁ : ∀ x : A, B₁ * (A₁ * x) = A₁ * (B₁ * x) := by
    intro x; rw [← mul_assoc, ← T.A₁B₁_commutes, mul_assoc]
  have e4 : (4 : A) = 1 + 1 + 1 + 1 := by norm_num
  unfold chshOp
  rw [e4]
  noncomm_ring
  simp only [d₀₀, d₀₁, d₁₀, d₁₁, hA₀, hA₁, sA₀, sA₁, sB₀, sB₁, mul_one]
  abel

/-- The CHSH operator of a CHSH tuple is self-adjoint. -/
theorem isSelfAdjoint_chshOp (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    IsSelfAdjoint (chshOp A₀ A₁ B₀ B₁) := by
  unfold IsSelfAdjoint chshOp
  simp only [star_sub, star_add, star_mul, T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa,
    ← T.A₀B₀_commutes, ← T.A₀B₁_commutes, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]

end Ring

section CStar

variable [NormedRing A] [StarRing A] [CStarRing A] [NormOneClass A] {A₀ A₁ B₀ B₁ : A}

/-- A self-adjoint involution in a C⋆-algebra has norm one. -/
theorem norm_eq_one_of_sa_involution {x : A} (hsa : star x = x) (hx : x ^ 2 = 1) :
    ‖x‖ = 1 := by
  have h : ‖x‖ * ‖x‖ = 1 := by
    have := CStarRing.norm_star_mul_self (x := x)
    rw [hsa] at this
    rw [← this, ← sq, hx, norm_one]
  nlinarith [norm_nonneg x]

omit [StarRing A] [CStarRing A] [NormOneClass A] in
/-- The norm of a commutator of two elements of norm one is at most `2`. -/
theorem norm_commutator_le {x y : A} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x * y - y * x‖ ≤ 2 := by
  calc ‖x * y - y * x‖ ≤ ‖x * y‖ + ‖y * x‖ := norm_sub_le _ _
    _ ≤ ‖x‖ * ‖y‖ + ‖y‖ * ‖x‖ := by gcongr <;> exact norm_mul_le _ _
    _ = 2 := by rw [hx, hy]; norm_num

/-- **Tsirelson's bound**: in a C⋆-algebra, the CHSH operator built from a CHSH tuple
(two pairs of self-adjoint observables squaring to one, with Alice's commuting with Bob's)
has operator norm at most `2√2`. -/
theorem chsh_tsirelson (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖chshOp A₀ A₁ B₀ B₁‖ ≤ 2 * Real.sqrt 2 := by
  set C : A := chshOp A₀ A₁ B₀ B₁
  have hnA₀ : ‖A₀‖ = 1 := norm_eq_one_of_sa_involution T.A₀_sa T.A₀_inv
  have hnA₁ : ‖A₁‖ = 1 := norm_eq_one_of_sa_involution T.A₁_sa T.A₁_inv
  have hnB₀ : ‖B₀‖ = 1 := norm_eq_one_of_sa_involution T.B₀_sa T.B₀_inv
  have hnB₁ : ‖B₁‖ = 1 := norm_eq_one_of_sa_involution T.B₁_sa T.B₁_inv
  have hcommA : ‖A₀ * A₁ - A₁ * A₀‖ ≤ 2 := norm_commutator_le hnA₀ hnA₁
  have hcommB : ‖B₀ * B₁ - B₁ * B₀‖ ≤ 2 := norm_commutator_le hnB₀ hnB₁
  have h4 : ‖(4 : A)‖ ≤ 4 := by
    have e4 : (4 : A) = 1 + 1 + 1 + 1 := by norm_num
    rw [e4]
    calc ‖(1 : A) + 1 + 1 + 1‖ ≤ ‖(1 : A) + 1 + 1‖ + ‖(1 : A)‖ := norm_add_le _ _
      _ ≤ (‖(1 : A) + 1‖ + ‖(1 : A)‖) + ‖(1 : A)‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖(1 : A)‖ + ‖(1 : A)‖) + ‖(1 : A)‖) + ‖(1 : A)‖ := by gcongr; exact norm_add_le _ _
      _ = 4 := by rw [norm_one]; norm_num
  have hsq : ‖C‖ * ‖C‖ ≤ 8 := by
    have hstar : star C * C = C * C := by rw [(isSelfAdjoint_chshOp T : star C = C)]
    have : ‖C‖ * ‖C‖ = ‖C * C‖ := by
      rw [← CStarRing.norm_star_mul_self, hstar]
    rw [this, chshOp_mul_self T]
    calc ‖(4 : A) - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀)‖
        ≤ ‖(4 : A)‖ + ‖(A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀)‖ := norm_sub_le _ _
      _ ≤ 4 + ‖A₀ * A₁ - A₁ * A₀‖ * ‖B₀ * B₁ - B₁ * B₀‖ := by
            gcongr; exact norm_mul_le _ _
      _ ≤ 4 + 2 * 2 := by gcongr
      _ = 8 := by norm_num
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [norm_nonneg C, Real.sqrt_nonneg 2]

end CStar

end QC

