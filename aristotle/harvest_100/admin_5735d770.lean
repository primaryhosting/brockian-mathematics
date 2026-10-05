/-
# Conjecture Statement
Category: Frontier — Prime Numbers
Target: Goldbach.conjecture_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

/-- The strong Goldbach conjecture, stated (not proved) as a `Prop`:
every even natural number greater than `2` is a sum of two primes. -/
def Goldbach : Prop :=
  ∀ n : Nat, 2 < n → Even n → ∃ p q : Nat, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- The trivial self-equivalence of the strong Goldbach conjecture:
`Goldbach ↔ Goldbach`.  This does not prove (or disprove) the conjecture itself. -/
theorem Goldbach.conjecture_statement : Goldbach ↔ Goldbach := Iff.rfl

#print axioms Goldbach.conjecture_statement

