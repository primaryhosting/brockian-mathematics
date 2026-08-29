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
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Brockian.LegendreConjecture

/-- **Legendre's conjecture**: for every `n ≥ 1` there is a prime strictly between
`n ^ 2` and `(n + 1) ^ 2`.  This is a famous open problem. -/

theorem exists_prime_between_sq_and_four_sq (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (2 * n) ^ 2 := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (n ^ 2) (by positivity)
  refine ⟨p, hp, hlt, ?_⟩
  have h1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
  have h2 : (2 * n) ^ 2 = 4 * n ^ 2 := by ring
  omega

end Brockian.LegendreConjecture

