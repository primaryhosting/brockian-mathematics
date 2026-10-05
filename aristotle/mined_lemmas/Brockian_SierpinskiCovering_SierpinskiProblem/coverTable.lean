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
# Sierpinski Problem
Category: Brockian Conjecture
Target: Brockian.SierpinskiCovering.SierpinskiProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Brockian
namespace SierpinskiCovering

/-- The covering table: for a residue `r` of the exponent modulo `36`, this list records a
small prime that divides `78557 * 2 ^ r + 1` (and also divides `2 ^ 36 - 1`, so that the
divisibility only depends on the exponent modulo `36`).

The primes used are `3, 5, 7, 13, 19, 37, 73`, which form the classical covering system
for the Sierpiński number `78557`. -/

def coverTable : List ℕ :=
  [3, 5, 3, 73, 3, 5, 3, 7, 3, 5, 3, 13, 3, 5, 3, 19, 3, 5, 3, 7,
   3, 5, 3, 13, 3, 5, 3, 37, 3, 5, 3, 7, 3, 5, 3, 13]

/-- The prime of the covering system attached to an exponent `n`, namely the entry of
`coverTable` at index `n % 36`. -/
