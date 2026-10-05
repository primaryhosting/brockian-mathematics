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

lemma eq_of_orderOf_eq {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hrq : r ∣ 2 * p + 1)
    (hord : orderOf (2 : ZMod r) = p) : r = 2 * p + 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hdvd : p ∣ r - 1 := by
    have h1 := ZMod.pow_card_sub_one_eq_one (two_ne_zero_of_dvd (p := p) hr hrq)
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rwa [hord] at h2
  have hle : r ≤ 2 * p + 1 := Nat.le_of_dvd (by omega) hrq
  have hr2 : 2 ≤ r := hr.two_le
  obtain ⟨k, hk⟩ := hdvd
  have hp2 : 2 ≤ p := hp.two_le
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · omega
    · omega
  have hk' : r = p * k + 1 := by omega
  have hk2 : k ≤ 2 := by
    have hmul : p * k ≤ p * 2 := by omega
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
  interval_cases k
  · -- `r = p + 1` : then `p + 1` divides both `2 * p + 2` and `2 * p + 1`, hence divides `1`.
    exfalso
    have h1 : r ∣ 2 * p + 2 := ⟨2, by omega⟩
    have h2 : r ∣ 1 := by
      have := Nat.dvd_sub h1 hrq
      simpa using this
    have := Nat.le_of_dvd one_pos h2
    omega
  · omega

/-- The order of `2` modulo a prime `r` is never `1`. -/
