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

theorem gbCheck_spec {n : ℕ} (hn : n < 1681) (h : gbCheck n = true) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  rw [gbCheck, List.any_eq_true] at h
  obtain ⟨p, hp, hcond⟩ := h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hcond
  obtain ⟨⟨hple, hpp⟩, hqp⟩ := hcond
  have hpb : p < 1681 := by
    have : ∀ x ∈ wheelPrimes, x < 1681 := by decide
    exact this p hp
  refine ⟨p, n - p, isPrimeB_spec hpb hpp, isPrimeB_spec (by omega) hqp, by omega⟩

/-- The finite verification underlying the wheel: the boolean Goldbach check succeeds for
every even number between `4` and `1456`. -/
