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
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace RepunitPrimes

/-- The `n`-th repunit: the base-ten number consisting of `n` digits `1`,
i.e. `repunit n = (10 ^ n - 1) / 9`. -/

theorem exists_pos_dvd_repunit {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h5 : p ≠ 5) :
    ∃ n, 0 < n ∧ p ∣ repunit n := by
  by_cases h3 : p = 3
  · exact ⟨3, by norm_num, by subst h3; decide⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hp10 : ¬ (p ∣ 10) := by
    intro h
    have h25 : p ∣ 2 * 5 := by norm_num at h ⊢; exact h
    rcases (Nat.Prime.dvd_mul hp).mp h25 with h' | h'
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')
    · exact h5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h')
  have h10 : (10 : ZMod p) ≠ 0 := fun h =>
    hp10 ((ZMod.natCast_eq_zero_iff 10 p).mp (by push_cast; exact h))
  have hferm : (10 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h10
  have hkey : ((9 * repunit (p - 1) + 1 : ℕ) : ZMod p) = ((10 ^ (p - 1) : ℕ) : ZMod p) := by
    rw [nine_mul_repunit_add_one]
  push_cast at hkey
  rw [hferm] at hkey
  have h9 : (9 : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 9 := (ZMod.natCast_eq_zero_iff 9 p).mp (by push_cast; exact h)
    have h32 : p ∣ 3 ^ 2 := by norm_num at hd ⊢; exact hd
    exact h3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h32))
  have hR : ((repunit (p - 1) : ℕ) : ZMod p) = 0 := by
    have hz : (9 : ZMod p) * (repunit (p - 1) : ZMod p) = 0 := by linear_combination hkey
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h h9
    · exact h
  refine ⟨p - 1, ?_, (ZMod.natCast_eq_zero_iff _ p).mp hR⟩
  have := hp.two_le
  omega

/-- The set of primes dividing some repunit. -/
