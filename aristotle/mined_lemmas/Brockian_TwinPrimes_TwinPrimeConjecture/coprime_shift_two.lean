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
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.TwinPrimes

open Nat

/-- `p` is a twin prime (the smaller member of a twin prime pair) if both `p` and `p + 2`
are prime. -/

private lemma coprime_shift_two (j : ℕ) : Nat.Coprime (2 * j + 3) (2 * j + 5) := by
  have h1 := Nat.gcd_dvd_left (2 * j + 3) (2 * j + 5)
  have h2 := Nat.gcd_dvd_right (2 * j + 3) (2 * j + 5)
  have hd : Nat.gcd (2 * j + 3) (2 * j + 5) ∣ 2 :=
    (Nat.dvd_add_iff_right h1).mpr (by simp [show 2 * j + 5 = (2 * j + 3) + 2 from rfl] at h2 ⊢)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact h
  · rw [h] at h1; omega

/-- If `k + 5` is prime then, modulo `k + 5`, one has `2 * (k + 2)! = -1`. -/
