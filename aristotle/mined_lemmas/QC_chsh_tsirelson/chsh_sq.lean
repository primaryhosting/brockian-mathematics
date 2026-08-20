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
