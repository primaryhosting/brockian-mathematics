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

theorem isPrimeNat_2293 : IsPrimeNat 2293 := by
  refine isPrimeNat_of_no_divisor_le_sqrt (by omega) ?_
  have key : ∀ m : Nat, m < 48 → 2 ≤ m → ¬ m ∣ 2293 := by decide
  intro m hm2 hsq
  refine key m ?_ hm2
  rcases Nat.lt_or_ge m 48 with h | h
  · exact h
  · have : 48 * 48 ≤ m * m := Nat.mul_le_mul h h
    omega

/--
**Goldbach wheel, `K = 2`, new wheel modulus `1153`.**

The wheel modulus `1153` is prime, and the associated even number `2 * 1153 = 2306` has a
Goldbach representation as a sum of `K = 2` primes, each of which is a unit of the wheel,
i.e. not divisible by the modulus `1153`.

Witnesses: `2306 = 13 + 2293`, with `13` and `2293` prime.
-/
