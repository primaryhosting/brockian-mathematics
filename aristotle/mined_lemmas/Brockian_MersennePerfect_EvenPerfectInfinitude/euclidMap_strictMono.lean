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
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Even Perfect Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.EvenPerfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The infinitude of even perfect numbers is equivalent to the infinitude of Mersenne primes,
which is a well-known open problem.  What is proved here is therefore the (unconditional)
*reduction*: the set of even perfect numbers is infinite **iff** the set of exponents `p`
with `2 ^ p - 1` prime is infinite.

The Euclid–Euler development below (`sigma_two_pow_eq_mersenne_succ`,
`perfect_two_pow_mul_mersenne_of_prime`, `eq_two_pow_mul_prime_mersenne_of_even_perfect`,
`even_and_perfect_iff`) follows the proof of Theorem 70 of the 100 theorems list as
developed by Aaron Anderson in the Mathlib `Archive` (Apache 2.0); it is reproduced here
because the `Archive` is not part of the importable `Mathlib` library.
-/

namespace Brockian.MersennePerfect

open Nat ArithmeticFunction Finset

open scoped sigma

/-! ## The Euclid–Euler theorem -/


theorem euclidMap_strictMono : StrictMono euclidMap := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h1 : 0 < 2 ^ k := Nat.two_pow_pos k
  have h2 : (2 : ℕ) ^ (k + 1) ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
  simp only [euclidMap, mersenne]
  calc 2 ^ k * (2 ^ (k + 1) - 1) < 2 ^ (k + 1) * (2 ^ (k + 1) - 1) :=
        (Nat.mul_lt_mul_right (by omega)).mpr (by omega)
    _ ≤ 2 ^ (k + 1) * (2 ^ (k + 2) - 1) := Nat.mul_le_mul_left _ (by omega)

