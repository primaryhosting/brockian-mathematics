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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Tsirelson's bound for the CHSH operator in a C*-algebra

Given a CHSH tuple `(A₀, A₁, B₀, B₁)` in a unital C*-algebra (four self-adjoint
involutions such that the `Aᵢ` commute with the `Bⱼ`), the CHSH operator

`C = A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁`

satisfies `‖C‖ ≤ 2 * √2`.

The proof is the classical one: `C` is self-adjoint and
`C * C = 4 - [A₀, A₁] * [B₀, B₁]`, where each commutator has norm at most `2`.
Hence `‖C‖ ^ 2 = ‖C * C‖ ≤ 4 + 4 = 8` by the C*-identity.
-/

namespace QC

section Algebra

variable {A : Type*} [Ring A]

/-- The square of the CHSH operator equals `4 - [A₀, A₁] * [B₀, B₁]`. -/

theorem chsh_sq_eq {A₀ A₁ B₀ B₁ : A}
    (hA0 : A₀ * A₀ = 1) (hA1 : A₁ * A₁ = 1) (hB0 : B₀ * B₀ = 1) (hB1 : B₁ * B₁ = 1)
    (c00 : A₀ * B₀ = B₀ * A₀) (c01 : A₀ * B₁ = B₁ * A₀)
    (c10 : A₁ * B₀ = B₀ * A₁) (c11 : A₁ * B₁ = B₁ * A₁) :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) * (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁)
      = 4 - (A₀ * A₁ - A₁ * A₀) * (B₀ * B₁ - B₁ * B₀) := by
  have s00 : ∀ x : A, B₀ * (A₀ * x) = A₀ * (B₀ * x) := by
    intro x; rw [← mul_assoc, ← c00, mul_assoc]
  have s01 : ∀ x : A, B₁ * (A₀ * x) = A₀ * (B₁ * x) := by
    intro x; rw [← mul_assoc, ← c01, mul_assoc]
  have s10 : ∀ x : A, B₀ * (A₁ * x) = A₁ * (B₀ * x) := by
    intro x; rw [← mul_assoc, ← c10, mul_assoc]
  have s11 : ∀ x : A, B₁ * (A₁ * x) = A₁ * (B₁ * x) := by
    intro x; rw [← mul_assoc, ← c11, mul_assoc]
  have q0 : ∀ x : A, A₀ * (A₀ * x) = x := by intro x; rw [← mul_assoc, hA0, one_mul]
  have q1 : ∀ x : A, A₁ * (A₁ * x) = x := by intro x; rw [← mul_assoc, hA1, one_mul]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_assoc,
    s00, s01, s10, s11, q0, q1, hA0, hA1, hB0, hB1, mul_one]
  abel_nf
  simp
  abel

end Algebra

section CStar

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A] [NormOneClass A]

/-- A self-adjoint involution in a unital C*-algebra has norm `1`. -/
