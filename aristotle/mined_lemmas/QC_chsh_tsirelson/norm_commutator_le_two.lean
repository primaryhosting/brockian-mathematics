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

theorem norm_commutator_le_two {a b : A} (ha : star a = a) (hb : star b = b)
    (ha2 : a * a = 1) (hb2 : b * b = 1) : ‖a * b - b * a‖ ≤ 2 := by
  have hna : ‖a‖ = 1 := norm_eq_one_of_sa_involution ha ha2
  have hnb : ‖b‖ = 1 := norm_eq_one_of_sa_involution hb hb2
  calc ‖a * b - b * a‖ ≤ ‖a * b‖ + ‖b * a‖ := norm_sub_le _ _
    _ ≤ ‖a‖ * ‖b‖ + ‖b‖ * ‖a‖ := by gcongr <;> exact norm_mul_le _ _
    _ = 2 := by rw [hna, hnb]; norm_num

/-- **Tsirelson's bound**: in a unital C*-algebra, the CHSH operator built from a CHSH tuple
`(A₀, A₁, B₀, B₁)` (self-adjoint involutions, with the `Aᵢ` commuting with the `Bⱼ`) has
operator norm at most `2 * √2`. -/
