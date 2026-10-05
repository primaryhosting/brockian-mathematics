import Brockian.MersennePerfect

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

(Note: written as a plain block comment rather than a module docstring, since Lean 4
requires `import` commands to precede any module docstring.)
-/

import Mathlib

namespace Brockian.MersennePerfect

open Finset

/-- The set of exponents `p` for which the Mersenne number `2 ^ p - 1` is prime. -/

lemma sum_divisors_two_pow_mul_odd (k : ℕ) {m : ℕ} (hm : Odd m) :
    ∑ i ∈ (2 ^ k * m).divisors, i = (2 ^ (k + 1) - 1) * ∑ i ∈ m.divisors, i := by
  have hcop : Nat.Coprime (2 ^ k) m :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
  have hmul : ∑ i ∈ (2 ^ k * m).divisors, i
      = (∑ i ∈ (2 ^ k : ℕ).divisors, i) * (∑ i ∈ m.divisors, i) := by
    have := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime hcop
    simpa [ArithmeticFunction.sigma_one_apply] using this
  rw [hmul, Nat.sum_divisors_prime_pow Nat.prime_two, sum_range_two_pow]

/-- **Euler's theorem on even perfect numbers**: every even perfect number has the form
`2 ^ k * (2 ^ (k+1) - 1)` with `2 ^ (k+1) - 1` prime. -/
