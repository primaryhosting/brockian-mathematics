import Mathlib
/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
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

/-- `a : ℤ` is a *primitive root* modulo `p` when the image of `a` in `ZMod p` has
multiplicative order exactly `p - 1`, i.e. it generates the group of units of `ZMod p`. -/

theorem eq_two_of_isSquare_of_isPrimitiveRootMod {a : ℤ} {p : ℕ} (hp : Nat.Prime p)
    (hsq : IsSquare a) (h : IsPrimitiveRootMod a p) : p = 2 := by
  unfold IsPrimitiveRootMod at h
  by_contra hne
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hne
  obtain ⟨b, rfl⟩ := hsq
  have hp2 : 2 ≤ p := hp.two_le
  set x : ZMod p := (b : ZMod p) with hx
  have hcast : ((b * b : ℤ) : ZMod p) = x * x := by push_cast [hx]; ring
  rw [hcast] at h
  have hx0 : x ≠ 0 := by
    rintro h0
    rw [h0] at h
    simp at h
    omega
  have hpow : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx0
  have h2 : (x * x) ^ ((p - 1) / 2) = 1 := by
    rw [← sq, ← pow_mul]
    have h3 : 2 * ((p - 1) / 2) = p - 1 := by obtain ⟨k, hk⟩ := hodd; omega
    rw [h3, hpow]
  have hdvd := orderOf_dvd_of_pow_eq_one h2
  rw [h] at hdvd
  have hpos : 0 < (p - 1) / 2 := by
    have h3 : 3 ≤ p := by omega
    omega
  have := Nat.le_of_dvd hpos hdvd
  omega

/-- `-1` can only be a primitive root modulo `2` and `3`. -/
