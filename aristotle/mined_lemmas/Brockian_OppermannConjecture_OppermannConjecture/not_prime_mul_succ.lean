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
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Brockian.OppermannConjecture

/-- Oppermann's property for `n`: there is a prime strictly between `n(n-1)` and `n²`,
and a prime strictly between `n²` and `n(n+1)`. -/

lemma not_prime_mul_succ {n : ℕ} (h2 : 2 ≤ n) : ¬ Nat.Prime (n * n + n) := by
  intro hp
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp n ⟨n + 1, by ring⟩) with h | h <;> nlinarith

/-- Oppermann's property is equivalent to the classical statement
`π(n² - n) < π(n²) < π(n² + n)` in terms of the prime counting function. -/
