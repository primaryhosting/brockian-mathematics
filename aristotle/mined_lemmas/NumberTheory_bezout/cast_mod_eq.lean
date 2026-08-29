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

/-!
# Bezout
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.bezout
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- Rewriting the natural-number remainder as an integer linear expression. -/

private theorem cast_mod_eq (m n : Nat) :
    ((n % m : Nat) : Int) = (n : Int) - (m : Int) * ((n / m : Nat) : Int) := by
  have h := Nat.div_add_mod n m
  omega

/-- Bézout's identity for natural numbers, proved by the Euclidean recursion. -/
