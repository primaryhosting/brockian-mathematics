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

theorem GoldbachWheelK2_727 :
    ∀ r : ZMod 727, ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ (p : ZMod 727) + (q : ZMod 727) = r := by
  intro r
  set v : ℕ := r.val with hv
  have hvlt : v < 727 := ZMod.val_lt r
  have hvr : (v : ZMod 727) = r := by
    simp [hv, ZMod.natCast_val, ZMod.cast_id]
  -- choose an even representative `n` of `r` in the range `[4, 1456]`
  obtain ⟨n, hn1, hn2, hn3, hn4⟩ :
      ∃ n : ℕ, Even n ∧ 4 ≤ n ∧ n ≤ 1456 ∧ (n : ZMod 727) = r := by
    rcases Nat.even_or_odd v with he | ho
    · rcases lt_or_ge v 4 with hlt | hge
      · obtain ⟨t, ht⟩ := he
        refine ⟨v + 1454, ⟨t + 727, by omega⟩, by omega, by omega, ?_⟩
        · have h1454 : ((1454 : ℕ) : ZMod 727) = 0 := by decide
          rw [Nat.cast_add, hvr, h1454, add_zero]
      · exact ⟨v, he, hge, by omega, hvr⟩
    · refine ⟨v + 727, ?_, by omega, by omega, ?_⟩
      · rcases ho with ⟨t, ht⟩; exact ⟨t + 364, by omega⟩
      · have h727 : ((727 : ℕ) : ZMod 727) = 0 := by decide
        rw [Nat.cast_add, hvr, h727, add_zero]
  obtain ⟨p, q, hp, hq, hpq⟩ := goldbach_even_le_1456 hn1 hn2 hn3
  refine ⟨p, q, hp, hq, ?_⟩
  rw [← hn4, ← hpq]
  push_cast
  ring

end Brockian

