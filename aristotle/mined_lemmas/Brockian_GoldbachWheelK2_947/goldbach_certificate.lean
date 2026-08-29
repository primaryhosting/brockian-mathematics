/-
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the header above is
-- rendered as a plain block comment; the identical module docstring follows the import.)

import Mathlib

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 400000
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

/-- A kernel-friendly primality test: trial division by all candidate divisors `< 47`.
It is a correct primality test for every `n < 47 ^ 2 = 2209`, see `Brockian.isPSmall_iff`. -/

theorem goldbach_certificate :
    ∀ n < 1895, 4 ≤ n → n % 2 = 0 → ∃ p < 80, isPSmall p ∧ isPSmall (n - p) := by
  decide +kernel

/-- **Goldbach wheel, `K = 2`, modulus `947`.**
Every even natural number `n` with `4 ≤ n ≤ 2 * 947 = 1894` is a sum of two primes. -/
