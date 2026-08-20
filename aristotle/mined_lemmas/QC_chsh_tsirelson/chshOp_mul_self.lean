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
