/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- This module is deliberately import-free (Lean forbids `import` after the header
-- comment above), so primality is spelled out from first principles here.  The
-- companion module `RequestProject.GoldbachWheelK2_1327Mathlib` proves that
-- `Brockian.IsPrimeNat` coincides with Mathlib's `Nat.Prime`, and restates the
-- main theorem in Mathlib's vocabulary.

namespace Brockian

set_option maxRecDepth 100000

/-- Primality, from first principles: `n` is at least `2` and its only divisors are
`1` and `n`. -/

theorem goldbach_all_check :
    ((List.range 2655).all fun n => !(decide (4 ≤ n ∧ n % 2 = 0)) || goldbachCheck n) = true := by
  decide +kernel

/--
**Goldbach wheel with `K = 2` and wheel modulus `1327`.**

The modulus `1327` is prime, and every even `n` with `4 ≤ n ≤ 2 * 1327` is a sum of two
primes `p + q` in which the wheel summand `p` may always be taken with `p ≤ 103`
(a bound that is attained in this range).
-/
