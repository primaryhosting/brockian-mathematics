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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

open Finset Pointwise

/-! ## Basic definitions -/

/-- The sum of the (positive) divisors of `n`. -/

lemma sigma1_mul_prime_pow_succ {n p j : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    sigma1 (n * p ^ (j + 1)) = p ^ (j + 1) * sigma1 n + sigma1 (n * p ^ j) := by
  unfold sigma1
  rw [divisors_mul_prime_pow_succ hp,
    Finset.sum_union (disjoint_divisors_mul_prime_pow hp hpn),
    sum_mul_singleton (pow_pos hp.pos _)]

/-! ## The key covering step -/

