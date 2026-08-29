/-
# Cassini 15
Category: Pure Mathematics
Target: Math.cassini_15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: the header above uses a plain block comment `/- -/` rather than a module
-- docstring `/-! -/`, since Lean requires `import` commands to precede any module
-- docstring. The text is otherwise verbatim as requested.

import Mathlib

namespace Math

/-- Cassini's identity at `n = 15`: `F(14) * F(16) - F(15)^2 = (-1)^15`. -/
theorem cassini_15 :
    (Nat.fib 14 : ℤ) * (Nat.fib 16 : ℤ) - (Nat.fib 15 : ℤ) ^ 2 = (-1) ^ 15 := by
  norm_num [Nat.fib]

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

