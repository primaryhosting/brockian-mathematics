import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option maxRecDepth 100000

namespace Brockian

/-- The "spokes" of the wheel: the small primes that are used as the smaller summand
in the Goldbach decompositions below.  (For every even `n ≤ 1051` one of these works.) -/

theorem goldbachCheck_1052 : goldbachCheck 1052 = true := by decide +kernel

/-- **Goldbach wheel, K = 2, modulus 1051.**
Every even natural number `n` with `4 ≤ n ≤ 1051` is a sum of two primes. -/
