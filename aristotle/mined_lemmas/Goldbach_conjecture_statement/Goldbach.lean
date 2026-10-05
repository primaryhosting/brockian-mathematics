import Mathlib

/-!
# Conjecture Statement
Category: Frontier — Prime Numbers
Target: Goldbach.conjecture_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The strong Goldbach conjecture: every even natural number greater than `2`
is the sum of two primes. This is only *stated* here, never proved. -/

def Goldbach : Prop :=
  ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

namespace Goldbach

/-- The trivial self-equivalence of the strong Goldbach conjecture:
`Goldbach ↔ Goldbach`. Proved by splitting the biconditional into its two
implications and discharging each branch with the assumed hypothesis. -/
