/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required header above is a module doc comment, and Lean 4 forbids any
`import` after it, so this file is written in pure core Lean (no Mathlib) and is fully
self-contained.  The file `RequestProject/GoldbachWheelK2_1153Mathlib.lean` imports Mathlib and
this file, proves `Brockian.IsPrimeNat n ↔ Nat.Prime n`, and restates the result in Mathlib
vocabulary.
-/

namespace Brockian

/-- A natural number is prime when it is at least `2` and its only divisors are `1` and itself. -/

theorem isPrimeNat_13 : IsPrimeNat 13 := by
  refine isPrimeNat_of_no_divisor_le_sqrt (by omega) ?_
  have key : ∀ m : Nat, m < 4 → 2 ≤ m → ¬ m ∣ 13 := by decide
  intro m hm2 hsq
  refine key m ?_ hm2
  rcases Nat.lt_or_ge m 4 with h | h
  · exact h
  · have : 4 * 4 ≤ m * m := Nat.mul_le_mul h h
    omega

