/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
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

namespace Brockian

/-- A trial-division primality test, valid for `n ≤ 727` (since `27 * 27 = 729 > 727`,
it suffices to rule out divisors `d` with `2 ≤ d < 27`). -/

theorem wheelGoldbachTest_sound {n : ℕ} (hn : n ≤ 727) (h : wheelGoldbachTest n = true) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  rw [wheelGoldbachTest, List.any_eq_true] at h
  obtain ⟨p, hp, hpq⟩ := h
  rw [Bool.and_eq_true] at hpq
  obtain ⟨hp1, hp2⟩ := hpq
  have hple : p < 100 := List.mem_range.mp hp
  have hq2 : 2 ≤ n - p := by
    have := hp2
    rw [wheelPrimeTest, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  refine ⟨p, n - p, wheelPrimeTest_sound (by omega) hp1,
    wheelPrimeTest_sound (by omega) hp2, by omega⟩

/-- **Goldbach wheel, K = 2, modulus 727.**  Every even number `n` with `4 ≤ n ≤ 727`
is a sum of two primes. -/
