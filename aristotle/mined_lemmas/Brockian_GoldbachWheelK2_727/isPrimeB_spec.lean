/-
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to be the first command, so the header above is written as a
-- plain block comment; the identical text is repeated as a module docstring below.)

import Mathlib

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian

/-- Trial divisors: all primes below `41`.  A number `m < 41 ^ 2 = 1681` is prime iff it is
at least `2` and is not divisible by any of these (other than possibly being one of them). -/

theorem isPrimeB_spec {m : ℕ} (hm : m < 1681) (h : isPrimeB m = true) : Nat.Prime m := by
  rw [isPrimeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨h2, hall⟩ := h
  by_contra hp
  have hm1 : m ≠ 1 := by omega
  have hf : Nat.Prime (Nat.minFac m) := Nat.minFac_prime hm1
  have hdvd : Nat.minFac m ∣ m := Nat.minFac_dvd m
  have hsq : Nat.minFac m ^ 2 ≤ m := Nat.minFac_sq_le_self (by omega) hp
  have h41 : Nat.minFac m < 41 := by nlinarith [hf.two_le]
  have hmem : Nat.minFac m ∈ trialDivisors := by
    have h2' : 2 ≤ Nat.minFac m := hf.two_le
    rw [trialDivisors]
    interval_cases h : (Nat.minFac m) <;> revert hf <;> decide
  have := hall _ hmem
  rw [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
    Nat.dvd_iff_mod_eq_zero.symm] at this
  rcases this with heq | hnd
  · exact hp (heq ▸ hf)
  · exact hnd hdvd

/-- If the boolean Goldbach check succeeds on `n < 1681`, then `n` is a sum of two primes. -/
