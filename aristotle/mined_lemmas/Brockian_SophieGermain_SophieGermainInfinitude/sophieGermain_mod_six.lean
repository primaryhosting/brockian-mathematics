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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- A *Sophie Germain prime* is a prime `p` such that `2 * p + 1` is also prime. -/

theorem sophieGermain_mod_six {p : ℕ} (hp : IsSophieGermainPrime p) (h3 : 3 < p) :
    p % 6 = 5 := by
  obtain ⟨hp1, hp2⟩ := hp
  have h2 : ¬ (2 ∣ p) := by
    intro hd
    rcases (hp1.eq_one_or_self_of_dvd 2 hd) with h | h <;> omega
  have h3' : ¬ (3 ∣ p) := by
    intro hd
    rcases (hp1.eq_one_or_self_of_dvd 3 hd) with h | h <;> omega
  have hmod : p % 6 = 1 ∨ p % 6 = 5 := by
    rw [Nat.dvd_iff_mod_eq_zero] at h2 h3'
    omega
  rcases hmod with hm | hm
  · exfalso
    obtain ⟨k, hk⟩ : ∃ k, p = 6 * k + 1 := ⟨p / 6, by omega⟩
    have hdvd : 3 ∣ 2 * p + 1 := ⟨4 * k + 1, by omega⟩
    rcases (hp2.eq_one_or_self_of_dvd 3 hdvd) with h | h <;> omega
  · exact hm

/-- The Sophie Germain primes and the safe primes are in bijection via `p ↦ 2 * p + 1`,
so one family is infinite iff the other is. -/
