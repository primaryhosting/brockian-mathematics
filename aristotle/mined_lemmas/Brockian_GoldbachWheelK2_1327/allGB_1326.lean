import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-! ## A kernel-friendly primality test

Mathlib's `Decidable` instance for `Nat.Prime` performs a linear scan, which makes
`by decide` unusable for numbers of the size we need.  We therefore set up a trial
division test by divisors `≤ 63`, which is sound for all `n < 64 ^ 2 = 4096`.
-/

/-- `noSmallDiv n k = true` asserts that no `d` with `2 ≤ d ≤ k` and `d ≠ n` divides `n`. -/

private lemma allGB_1326 : allGB 1326 = true := by decide +kernel

/-- **New wheel modulus.** `1327` is a Goldbach K2 wheel modulus: it is prime, and every
even number `n` with `4 ≤ n ≤ 2654` is the sum of two primes. -/
