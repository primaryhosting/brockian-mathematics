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

theorem goldbach_even_le_1456 {n : ℕ} (hev : Even n) (h4 : 4 ≤ n) (hle : n ≤ 1456) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨k, hk⟩ := hev
  have hk' : n = 2 * k := by omega
  have hkr : k ∈ List.range 729 := by
    rw [List.mem_range]; omega
  have := (List.all_eq_true.1 gbCheck_all) k hkr
  rw [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h | h
  · omega
  · rw [hk']
    exact gbCheck_spec (by omega) h

/-- **Goldbach wheel of modulus 727, `K = 2`.**  Every residue class modulo `727` is
represented by a sum of two primes. -/
