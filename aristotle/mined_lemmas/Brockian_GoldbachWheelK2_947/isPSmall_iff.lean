/-
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- rendered as a plain block comment; the identical module docstring follows the import.)

import Mathlib

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 400000
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

/-- A kernel-friendly primality test: trial division by all candidate divisors `< 47`.
It is a correct primality test for every `n < 47 ^ 2 = 2209`, see `Brockian.isPSmall_iff`. -/

theorem isPSmall_iff {n : ℕ} (hn : n < 2209) : isPSmall n = true ↔ Nat.Prime n := by
  rw [isPSmall_eq_true_iff, Nat.prime_def_le_sqrt]
  have hsq : Nat.sqrt n < 47 := Nat.sqrt_lt'.mpr (by norm_num; omega)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun m hm hms hdvd => ?_⟩
    have hlt : Nat.sqrt n < n := Nat.sqrt_lt_self (by omega)
    exact h2 m (by omega) hm (by omega) (Nat.dvd_iff_mod_eq_zero.mp hdvd)
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun m _ hm hmn hmod => ?_⟩
    have hprime : Nat.Prime n := Nat.prime_def_le_sqrt.mpr ⟨h1, h2⟩
    have hdvd : m ∣ n := Nat.dvd_iff_mod_eq_zero.mpr hmod
    rcases hprime.eq_one_or_self_of_dvd m hdvd with h | h <;> omega

/-- The exhaustive Goldbach certificate for all even numbers up to `2 * 947 = 1894`:
each such `n` splits as `p + (n - p)` with both parts prime and with the small prime `p`
taken from the wheel spokes `p < 80`. -/
