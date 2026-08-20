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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is repeated below as a module docstring; Lean 4 does not allow a module
-- docstring to precede the `import` line.)
import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo the prime `p` when the residue of `a` generates the
multiplicative group of `ZMod p`, i.e. its multiplicative order is exactly `p - 1`. -/

theorem square_not_primitiveRoot {a : ℤ} (hsq : IsSquare a) {p : ℕ} (hp : p ∈ artinSet a) :
    p = 2 := by
  obtain ⟨hpp, hprim⟩ := hp
  haveI : Fact p.Prime := ⟨hpp⟩
  by_contra hne
  have hodd : Odd p := hpp.odd_of_ne_two hne
  obtain ⟨k, hk⟩ := hodd
  have hp2 := hpp.two_le
  obtain ⟨b, hb⟩ := hsq
  have hab : ((a : ZMod p)) = ((b : ZMod p)) ^ 2 := by
    rw [hb]; push_cast; ring
  unfold IsPrimitiveRootMod at hprim
  by_cases hb0 : ((b : ZMod p)) = 0
  · have ha0 : ((a : ZMod p)) = 0 := by rw [hab, hb0]; ring
    rw [ha0] at hprim
    have hz : orderOf (0 : ZMod p) = 0 := by
      apply orderOf_eq_zero
      rw [isOfFinOrder_iff_pow_eq_one]
      rintro ⟨n, hn, hpow⟩
      rw [zero_pow (by omega)] at hpow
      exact zero_ne_one hpow
    rw [hz] at hprim
    omega
  · have key : ((a : ZMod p)) ^ ((p - 1) / 2) = 1 := by
      rw [hab, ← pow_mul]
      have h2 : 2 * ((p - 1) / 2) = p - 1 := by omega
      rw [h2]
      exact ZMod.pow_card_sub_one_eq_one hb0
    have hdvd : orderOf ((a : ZMod p)) ∣ (p - 1) / 2 := orderOf_dvd_of_pow_eq_one key
    rw [hprim] at hdvd
    have hpos : 0 < (p - 1) / 2 := by omega
    have := Nat.le_of_dvd hpos hdvd
    omega

/-- `-1` is a primitive root only modulo primes `p ≤ 3`. -/
