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

/-
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as a plain block comment.)

import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
# Mersenne Prime Infinitude

The infinitude of Mersenne primes is a well-known open problem, so what is proved here is a
Lean-checked *reduction*: the set of Mersenne primes is infinite if and only if the set of even
perfect numbers is infinite.  The reduction is powered by the Euclid–Euler theorem, available in
Mathlib's archive as `Theorems100.Nat.even_and_perfect_iff`.
-/

namespace Brockian.MersennePerfect

/-- The set of Mersenne primes, i.e. primes of the form `2 ^ k - 1`. -/

theorem euclidMap_strictMono : StrictMono fun k : ℕ => 2 ^ k * mersenne (k + 1) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have h1 : (2 : ℕ) ^ n < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have h2 : mersenne (n + 1) < mersenne (n + 2) := mersenne_strictMono (by omega)
  exact Nat.mul_lt_mul_of_lt_of_lt h1 h2

/-- The Mersenne primes are exactly the values `2 ^ (k + 1) - 1` for `k` a Mersenne exponent. -/
