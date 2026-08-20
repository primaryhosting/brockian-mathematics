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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not allow a
-- module docstring to precede the `import` line.)

import Mathlib

namespace Brockian.AndricaConjecture

open scoped Nat

/-! ## The sequence of primes -/

/-- The set of primes is infinite. -/

def OppermannConjecture : Prop :=
  ∀ m : ℕ, 2 ≤ m →
    (∃ q, Nat.Prime q ∧ m ^ 2 - m < q ∧ q < m ^ 2) ∧
    (∃ q, Nat.Prime q ∧ m ^ 2 < q ∧ q < m ^ 2 + m)

/-! ## An unconditional reformulation -/

/-- Andrica's inequality at `n` is equivalent to the prime-gap bound
`p_{n+1} < p_n + 2√p_n + 1`. -/
