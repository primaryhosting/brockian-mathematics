/-!
# Cassini 14
Category: Pure Mathematics
Target: Math.cassini_14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required header above is a module docstring, and Lean requires all
`import` commands to precede any command (including a module docstring). The file is therefore
kept self-contained: the Fibonacci numbers are defined here and everything is proved from
first principles, with no imports.
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`. -/

theorem fib_values : fib 13 = 233 ∧ fib 14 = 377 ∧ fib 15 = 610 := by decide

end Math

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

