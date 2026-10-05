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

theorem wheelPrimeTest_sound {n : ℕ} (hn : n ≤ 727) (h : wheelPrimeTest n = true) :
    Nat.Prime n := by
  rw [wheelPrimeTest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨h2, hd⟩ := h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2, ?_⟩
  intro m hm hms hmd
  have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
  have hm27 : m < 27 := by nlinarith
  have := hd m (List.mem_range.mpr hm27)
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with (h1 | h1) | h1
  · omega
  · subst h1
    -- `m = n` would force `n ≤ Nat.sqrt n`, impossible for `2 ≤ n`
    have : Nat.sqrt m < m := Nat.sqrt_lt_self (by omega)
    omega
  · exact h1 hmd

