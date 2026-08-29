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

theorem isPrimeNat_1151 : IsPrimeNat 1151 := by decide

/-- `2` is prime. -/
