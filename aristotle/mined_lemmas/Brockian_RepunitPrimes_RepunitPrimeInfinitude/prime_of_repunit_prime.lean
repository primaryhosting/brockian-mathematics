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

namespace Brockian.RepunitPrimes

/-- The `n`-th base-ten repunit: the number `11…1` with `n` digits equal to `1`. -/

theorem prime_of_repunit_prime {n : ℕ} (hp : Nat.Prime (repunit n)) : Nat.Prime n := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [repunit_zero] at hp
    exact Nat.not_prime_zero hp
  have hn1 : n ≠ 1 := by
    rintro rfl
    rw [repunit_one] at hp
    exact Nat.not_prime_one hp
  rw [Nat.prime_def]
  refine ⟨by omega, ?_⟩
  intro d hd
  by_contra hcon
  push_neg at hcon
  obtain ⟨hd1, hdn⟩ := hcon
  have hdvd : repunit d ∣ repunit n := repunit_dvd_repunit hd
  have hdle : d ≤ n := Nat.le_of_dvd (by omega) hd
  have hdlt : d < n := lt_of_le_of_ne hdle hdn
  have h2 : 2 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · rw [Nat.zero_dvd] at hd; omega
    · omega
  have hlt : repunit d < repunit n := repunit_strictMono hdlt
  have hone : repunit d ≠ 1 := by
    have h11 : repunit 2 ≤ repunit d := repunit_strictMono.monotone h2
    rw [repunit_two] at h11
    omega
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact hone h
  · omega

/-- The set of repunit primes. -/
