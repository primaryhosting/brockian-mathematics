/-!
# Conjecture Statement
Category: Frontier — Prime Numbers
Target: Goldbach.conjecture_statement
Statement: State (do NOT prove) the strong Goldbach conjecture as a well-formed Prop and prove its trivial self-equivalence: define Goldbach := forall n : Nat, 2 < n -> Even n -> exists p q, Nat.Prime p and Nat.Prime q and p + q = n; then prove Goldbach <-> Goldbach.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
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

/-- The strong Goldbach conjecture: every even natural number greater than `2`
is the sum of two primes. This is only *stated*, not proved. -/
def Goldbach : Prop :=
  ∀ n : ℕ, 2 < n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- The trivial self-equivalence of the strong Goldbach conjecture. -/
theorem Goldbach.conjecture_statement : Goldbach ↔ Goldbach := Iff.rfl

#print axioms Goldbach.conjecture_statement

