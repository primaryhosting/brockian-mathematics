/-!
# Cassini 2
Category: Pure Mathematics
Target: Math.cassini_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires every `import` command to appear before any
other command, including a module docstring `/-! ... -/`.  Since this file must
*begin* with the header comment above, it cannot contain an `import Mathlib`
line.  We therefore give a self-contained development here (the Fibonacci
sequence is defined below), and additionally record the Mathlib-based version of
the same statement, phrased with `Nat.fib`, in `RequestProject/Main.lean`
(`Math.cassini_2_nat_fib`).
-/

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 2`: `F 1 * F 3 - F 2 ^ 2 = (-1) ^ 2`,
stated over the integers. -/
theorem cassini_2 :
    (fib 1 : Int) * (fib 3 : Int) - (fib 2 : Int) ^ 2 = (-1 : Int) ^ 2 := by
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

namespace Math

/-- Cassini's identity at `n = 2`, phrased with Mathlib's `Nat.fib`:
`F 1 * F 3 - F 2 ^ 2 = (-1) ^ 2`.  (Mathlib has no general Cassini identity
lemma at this version, so we compute directly.) -/
theorem cassini_2_nat_fib :
    (Nat.fib 1 : ℤ) * (Nat.fib 3 : ℤ) - (Nat.fib 2 : ℤ) ^ 2 = (-1 : ℤ) ^ 2 := by
  decide

end Math

