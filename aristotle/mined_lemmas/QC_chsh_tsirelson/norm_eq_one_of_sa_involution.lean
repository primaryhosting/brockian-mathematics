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

theorem norm_eq_one_of_sa_involution {a : A} (ha : star a = a) (h : a * a = 1) : ‖a‖ = 1 := by
  have h2 : ‖a‖ * ‖a‖ = 1 := by
    rw [← CStarRing.norm_star_mul_self (x := a), ha, h, norm_one]
  nlinarith [norm_nonneg a]

/-- The commutator of two self-adjoint involutions has norm at most `2`. -/
