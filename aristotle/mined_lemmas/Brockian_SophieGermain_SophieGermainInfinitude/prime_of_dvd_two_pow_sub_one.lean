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

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- `p` is a Sophie Germain prime if both `p` and `2 * p + 1` are prime. -/

theorem prime_of_dvd_two_pow_sub_one {p : ℕ} (hp : p.Prime) (h : (2 * p + 1) ∣ 2 ^ p - 1) :
    (2 * p + 1).Prime := by
  have hp2 : 2 ≤ p := hp.two_le
  have key : ∀ r : ℕ, r.Prime → r ∣ 2 * p + 1 → r = 2 * p + 1 := by
    intro r hr hrq
    haveI : Fact r.Prime := ⟨hr⟩
    have hrd : r ∣ 2 ^ p - 1 := hrq.trans h
    have hcast : ((2 ^ p - 1 : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ r).mpr hrd
    have hone : (1 : ℕ) ≤ 2 ^ p := Nat.one_le_two_pow
    rw [Nat.cast_sub hone] at hcast
    push_cast at hcast
    have hpow : (2 : ZMod r) ^ p = 1 := sub_eq_zero.mp hcast
    have hord : orderOf (2 : ZMod r) ∣ p := orderOf_dvd_of_pow_eq_one hpow
    rcases hp.eq_one_or_self_of_dvd _ hord with h1 | h1
    · exact absurd h1 (orderOf_two_ne_one hr)
    · exact eq_of_orderOf_eq hp hr hrq h1
  rw [Nat.prime_def_minFac]
  exact ⟨by omega, key _ (Nat.minFac_prime (by omega)) (Nat.minFac_dvd _)⟩

/-- **Criterion, plus case.** If `p` is prime and `2 * p + 1` divides `2 ^ p + 1`,
then `2 * p + 1` is prime. -/
