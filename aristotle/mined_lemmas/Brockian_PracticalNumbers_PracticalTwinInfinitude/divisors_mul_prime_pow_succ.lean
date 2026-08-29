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

lemma divisors_mul_prime_pow_succ {n p j : ℕ} (hp : p.Prime) :
    (n * p ^ (j + 1)).divisors = (n.divisors * {p ^ (j + 1)}) ∪ (n * p ^ j).divisors := by
  rw [Nat.divisors_mul, Nat.divisors_mul]
  have h : (p ^ (j + 1)).divisors = {p ^ (j + 1)} ∪ (p ^ j).divisors := by
    rw [Nat.divisors_prime_pow hp, Nat.divisors_prime_pow hp, Finset.range_add_one (n := j + 1)]
    ext x
    simp [Finset.mem_map, Finset.mem_range]
  rw [h, Finset.mul_union]

