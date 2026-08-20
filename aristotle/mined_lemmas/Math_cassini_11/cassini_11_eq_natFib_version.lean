/-!
# Cassini 11
Category: Pure Mathematics
Target: Math.cassini_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to be the very first commands of a
file, and a module docstring `/-! ... -/` counts as a command. Since the header comment above
must appear at the top of this file verbatim, this module is written without imports, using
its own definition of the Fibonacci sequence. The companion file
`RequestProject/Cassini11Mathlib.lean` imports Mathlib, proves that this definition agrees
with `Nat.fib`, and re-derives the same statement from Mathlib's general Cassini identity
`Int.fib_succ_mul_fib_pred_sub_fib_sq`.
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/

theorem cassini_11_eq_natFib_version :
    ((fib 10 : ℤ) * (fib 12 : ℤ) - (fib 11 : ℤ) ^ 2 = (-1) ^ 11) ↔
      ((Nat.fib 10 : ℤ) * (Nat.fib 12 : ℤ) - (Nat.fib 11 : ℤ) ^ 2 = (-1) ^ 11) := by
  simp [fib_eq_nat_fib]

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

