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

theorem dvd_of_sophieGermain {p : ℕ} (hp : p.Prime) (hq : (2 * p + 1).Prime) :
    (2 * p + 1) ∣ 2 ^ p - 1 ∨ (2 * p + 1) ∣ 2 ^ p + 1 := by
  set q := 2 * p + 1 with hqdef
  haveI : Fact q.Prime := ⟨hq⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hne : (2 : ZMod q) ≠ 0 := by
    intro hcon
    have hc : ((2 : ℕ) : ZMod q) = 0 := by push_cast; exact hcon
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 q).mp hc)
    omega
  have h1 : (2 : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne
  have h2 : ((2 : ZMod q) ^ p) * ((2 : ZMod q) ^ p) = 1 := by
    rw [← pow_add]
    have hpp : p + p = q - 1 := by omega
    rw [hpp]; exact h1
  rcases mul_self_eq_one_iff.mp h2 with h3 | h3
  · left
    have hz : ((2 ^ p - 1 : ℕ) : ZMod q) = 0 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]
      push_cast
      rw [h3]; ring
    exact (ZMod.natCast_eq_zero_iff _ q).mp hz
  · right
    have hz : ((2 ^ p + 1 : ℕ) : ZMod q) = 0 := by
      push_cast
      rw [h3]; ring
    exact (ZMod.natCast_eq_zero_iff _ q).mp hz

/-- The divisibility reformulation describes exactly the Sophie Germain primes. -/
