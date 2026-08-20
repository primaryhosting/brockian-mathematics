/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
set_option autoImplicit false

namespace Brockian

/-- Primality of a natural number, spelled out. This is equivalent to `Nat.Prime`; the
equivalence and a Mathlib-phrased restatement are in `RequestProject.Main`. -/

theorem isPrime_iff_nat_prime (p : ℕ) : IsPrime p ↔ Nat.Prime p :=
  Nat.prime_def.symm

/-- **Goldbach wheel, K = 2, modulus 727**, phrased with Mathlib's `Even` and `Nat.Prime`:
every even `n` with `4 ≤ n ≤ 2 * 727` is a sum of two primes, one of which lies in the fixed
12-element wheel `Brockian.goldbachWheelK2`. -/
