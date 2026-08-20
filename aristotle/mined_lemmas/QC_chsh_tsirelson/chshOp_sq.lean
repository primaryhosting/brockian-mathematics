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
