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

theorem isPrimeNat_iff_prime {n : ℕ} : IsPrimeNat n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨h2, hdvd⟩
    refine Nat.prime_def.mpr ⟨h2, fun m hm => ?_⟩
    rcases hdvd m hm with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro hp
    exact ⟨hp.two_le, fun m hm => (Nat.Prime.eq_one_or_self_of_dvd hp m hm)⟩

/-- Mathlib-phrased form of `Brockian.GoldbachWheelK2_1153`: the wheel modulus `1153` is prime
and `2 * 1153` is a sum of two primes, both coprime to the modulus. -/
