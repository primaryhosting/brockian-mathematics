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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect if `n = 1 + k * (σ n - n - 1)`, i.e. `n` is one plus `k` times the
sum of its proper divisors other than `1`.  The definition is stated in the subtraction-free
form `k * σ n + 1 = (k + 1) * n + k`. -/

theorem isKHyperperfect_mersenne {t : ℕ} (ht : 2 ≤ t) (hp : (2 ^ t - 1).Prime) :
    IsKHyperperfect 1 (2 ^ (t - 1) * (2 ^ t - 1)) := by
  have h2 : 2 ≤ 2 ^ t := by
    calc (2:ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) (by omega)
  simpa using isKHyperperfect_minoli Nat.prime_two hp ht (by omega)

/-- **Conditional reduction for the Brockian hyperperfect-infinitude conjecture.**

Fix a prime `q`.  If there are infinitely many exponents `t` for which `q ^ t - q + 1` is
prime, then there are infinitely many hyperperfect numbers.

Taking `q = 2` this says: infinitely many Mersenne primes imply infinitely many
(hyper)perfect numbers.  The unconditional infinitude of hyperperfect numbers is open. -/
