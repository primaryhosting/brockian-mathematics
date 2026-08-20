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

namespace Brockian.MersennePerfect

open ArithmeticFunction Finset
open scoped sigma

/-- The set of even perfect numbers. -/

lemma perfect_euclidMap {k : ℕ} (pr : Nat.Prime (mersenne (k + 1))) :
    Nat.Perfect (euclidMap k) := by
  have hpos : 0 < 2 ^ k * mersenne (k + 1) := by
    have := pr.pos
    positivity
  rw [euclidMap, Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime
      (((odd_mersenne_succ k).coprime_two_right).symm.pow_left _),
    sigma_one_two_pow]
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self,
    (Nat.sum_properDivisors_eq_one_iff_prime).2 pr,
    show (1:ℕ) + mersenne (k + 1) = 2 ^ (k + 1) from by rw [add_comm]; exact succ_mersenne _]
  ring

