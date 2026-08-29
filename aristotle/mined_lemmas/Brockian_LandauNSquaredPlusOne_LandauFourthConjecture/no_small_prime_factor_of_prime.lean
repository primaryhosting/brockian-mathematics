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
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LandauNSquaredPlusOne

/-- The set of natural numbers `n` such that `n ^ 2 + 1` is prime.
Landau's fourth problem asserts that this set is infinite; it is open. -/

theorem no_small_prime_factor_of_prime {n : ℕ} (hp : Nat.Prime (n ^ 2 + 1)) :
    ∀ p : ℕ, p.Prime → p ≤ n → ¬ p ∣ n ^ 2 + 1 := by
  intro p hpp hpn hdvd
  have heq : p = n ^ 2 + 1 := (Nat.prime_dvd_prime_iff_eq hpp hp).mp hdvd
  have : n ^ 2 + 1 ≤ n := heq ▸ hpn
  nlinarith [Nat.zero_le n, sq_nonneg n]

/-- **Equivalent reformulation of Landau's fourth problem.**  There are infinitely many
primes of the form `n ^ 2 + 1` if and only if for every bound there is a larger `n`
such that `n ^ 2 + 1` is divisible by no prime `p ≤ n`. -/
