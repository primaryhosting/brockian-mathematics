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
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to be the first command in a file, so the header above is a
-- plain block comment rather than a module docstring.)

import Mathlib

set_option maxRecDepth 40000

namespace Brockian.BrocardProblem

open Nat

/-- `IsBrocardSolution n m` says that `(n, m)` solves Brocard's equation `n! + 1 = m²`. -/

def isqrtFactorial (n : ℕ) : ℕ := sqrtTable.getD n 0

/-- The finite verification: for every `n ≤ 100` other than `4, 5, 7`, the number `n! + 1`
lies strictly between the consecutive squares `isqrtFactorial n ^ 2` and
`(isqrtFactorial n + 1) ^ 2`. -/
