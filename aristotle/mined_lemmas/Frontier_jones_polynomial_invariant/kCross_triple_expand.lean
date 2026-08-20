import Mathlib

/-!
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open LaurentPolynomial

/-! ## The coefficient ring of the Kauffman bracket -/

/-- The coefficient ring `ℤ[A, A⁻¹]` of the Kauffman bracket. -/
abbrev KRing : Type := LaurentPolynomial ℤ

/-- The Kauffman variable `A`. -/

theorem kCross_triple_expand (e₁ e₂ : S) (h₁ : e₁ * e₁ = delta • e₁)
    (h₁₂₁ : e₁ * (e₂ * e₁) = e₁) :
    kCross e₁ * kCross e₂ * kCross e₁
      = (A * A * A) • (1 : S) + A • e₁ + A • e₂ + Ainv • (e₁ * e₂) + Ainv • (e₂ * e₁) := by
  unfold kCross
  simp only [add_mul, mul_add, one_mul, mul_one, mul_assoc, h₁, h₁₂₁, smul_smul,
    mul_smul_comm, smul_mul_assoc]
  match_scalars <;>
    simp only [A, Ainv, delta, mul_one, mul_add, mul_sub, mul_neg, T_mul_T] <;>
    norm_num
  all_goals ring

/-- **Reidemeister III for the Kauffman bracket.**  The Kauffman resolutions of crossings
satisfy the braid relation, i.e. the Kauffman bracket is unchanged by a Reidemeister III
move. -/
