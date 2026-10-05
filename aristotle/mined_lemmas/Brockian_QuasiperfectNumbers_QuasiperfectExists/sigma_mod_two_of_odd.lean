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

import Mathlib

/-!
# Quasiperfect Exists
Category: Brockian Conjecture
Target: Brockian.QuasiperfectNumbers.QuasiperfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.QuasiperfectNumbers

open Finset

/-- A natural number `n` is *quasiperfect* if the sum of its divisors equals `2 * n + 1`,
i.e. the sum of its proper divisors is `n + 1`. -/

lemma sigma_mod_two_of_odd {n : ℕ} (hn : Odd n) :
    ArithmeticFunction.sigma 1 n % 2 = n.divisors.card % 2 := by
  have hall : ∀ d ∈ n.divisors, d % 2 = 1 := fun d hd =>
    Nat.odd_iff.mp (hn.of_dvd_nat (Nat.mem_divisors.mp hd).1)
  rw [sigma_one_eq_sum_divisors, Finset.sum_nat_mod, Finset.sum_congr rfl hall]
  simp

/-- An odd number with an odd sum of divisors is a perfect square. -/
