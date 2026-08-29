/-
# Cassini 10
Category: Pure Mathematics
Target: Math.cassini_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` commands to precede every other command, and a
-- module docstring `/-! ... -/` counts as a command. The header above is therefore
-- kept verbatim as a plain block comment so that the file compiles.

import Mathlib

namespace Math

/-- Cassini's identity at `n = 10`: `F(9) * F(11) - F(10)^2 = (-1)^10`,
i.e. `34 * 89 - 55^2 = 1`. -/
theorem cassini_10 :
    (Nat.fib 9 : ℤ) * (Nat.fib 11 : ℤ) - (Nat.fib 10 : ℤ) ^ 2 = (-1 : ℤ) ^ 10 := by
  have h9 : Nat.fib 9 = 34 := by decide
  have h10 : Nat.fib 10 = 55 := by decide
  have h11 : Nat.fib 11 = 89 := by decide
  rw [h9, h10, h11]
  norm_num

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

