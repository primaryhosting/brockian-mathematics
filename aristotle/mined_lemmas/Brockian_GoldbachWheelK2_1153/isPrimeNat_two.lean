/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, spelled out from first principles:
`p` is at least `2` and has no divisor `d` with `2 ≤ d < p`.
(This is proved equivalent to Mathlib's `Nat.Prime` in
`RequestProject/GoldbachWheelK2_1153Mathlib.lean`.) -/

theorem isPrimeNat_two : IsPrimeNat 2 := by decide

/-- **Goldbach wheel with `K = 2` at the modulus `1153`.**

The odd number `1153` is a sum of two primes, namely `1153 = 2 + 1151`, and this
decomposition is unique: any ordered pair of primes summing to `1153` is `(2, 1151)`
or `(1151, 2)`.  Thus the wheel of admissible prime pairs for `1153` collapses to the
single unordered pair `{2, 1151}`. -/
