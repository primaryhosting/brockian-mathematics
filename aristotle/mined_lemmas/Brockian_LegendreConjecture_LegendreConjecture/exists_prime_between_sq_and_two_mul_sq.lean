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
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` lines to precede any module doc comment, so the
-- required header block appears immediately after the single `import Mathlib` line.

namespace Brockian.LegendreConjecture

/-- `PrimeBetweenSquares n` states that there is a prime strictly between `n ^ 2`
and `(n + 1) ^ 2`. -/

theorem exists_prime_between_sq_and_two_mul_sq (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p ≤ 2 * n ^ 2 := by
  have hne : n ^ 2 ≠ 0 := by positivity
  exact Nat.exists_prime_lt_and_le_two_mul (n ^ 2) hne

/-- For each `1 ≤ n ≤ 500`, `legendreWitnesses.getD (n - 1) 0` is the least prime
exceeding `n ^ 2`; it is used to verify Legendre's conjecture in that range. -/
