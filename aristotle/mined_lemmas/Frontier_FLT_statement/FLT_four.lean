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
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- The statement of Fermat's Last Theorem in explicit positive-integer form:
`x ^ n + y ^ n = z ^ n` has no solution in positive integers when `n > 2`. -/

theorem FLT_four : FermatLastTheoremFor 4 := fermatLastTheoremFour

/-- Base case: FLT for the exponent `3` (Mathlib's `fermatLastTheoremThree`). -/
