/-
# Cassini 7
Category: Pure Mathematics
Target: Math.cassini_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: the header above uses `/- -/` rather than `/-! -/` because a module
-- docstring is a command and Lean requires `import` lines to come first.

import Mathlib

namespace Math

/-- Cassini's identity at `n = 7`: `F 6 * F 8 - F 7 ^ 2 = (-1) ^ 7`,
stated over the integers with Mathlib's `Nat.fib`.
(Mathlib has no general Cassini lemma; the numeric instance is decided directly.) -/
theorem cassini_7 : (Nat.fib 6 : ℤ) * (Nat.fib 8 : ℤ) - (Nat.fib 7 : ℤ) ^ 2 = (-1) ^ 7 := by
  decide

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

