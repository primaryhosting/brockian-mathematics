/-
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
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

namespace Math

set_option synthInstance.maxSize 1000000 in
set_option synthInstance.maxHeartbeats 4000000 in
set_option maxRecDepth 1000000 in
/-- Exhaustive check over the `2 ^ 15` two-colorings of the edges of `K₆`
(the edge between `i < j` is coloured `eij`): some triple `i < j < k` is
monochromatic. -/

private theorem mono_triangle_of_bools :
    ∀ e01 e02 e03 e04 e05 e12 e13 e14 e15 e23 e24 e25 e34 e35 e45 : Bool,
    (e01 = e12 ∧ e12 = e02) ∨
    (e01 = e13 ∧ e13 = e03) ∨
    (e01 = e14 ∧ e14 = e04) ∨
    (e01 = e15 ∧ e15 = e05) ∨
    (e02 = e23 ∧ e23 = e03) ∨
    (e02 = e24 ∧ e24 = e04) ∨
    (e02 = e25 ∧ e25 = e05) ∨
    (e03 = e34 ∧ e34 = e04) ∨
    (e03 = e35 ∧ e35 = e05) ∨
    (e04 = e45 ∧ e45 = e05) ∨
    (e12 = e23 ∧ e23 = e13) ∨
    (e12 = e24 ∧ e24 = e14) ∨
    (e12 = e25 ∧ e25 = e15) ∨
    (e13 = e34 ∧ e34 = e14) ∨
    (e13 = e35 ∧ e35 = e15) ∨
    (e14 = e45 ∧ e45 = e15) ∨
    (e23 = e34 ∧ e34 = e24) ∨
    (e23 = e35 ∧ e35 = e25) ∨
    (e24 = e45 ∧ e45 = e25) ∨
    (e34 = e45 ∧ e45 = e35) := by decide

/-- The 5-cycle colouring of the edges of `K₅`: `i` and `j` get colour `true`
exactly when they are consecutive modulo `5`. -/
