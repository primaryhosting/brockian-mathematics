/-!
# Cassini 3
Category: Pure Mathematics
Target: Math.cassini_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- NOTE: Lean 4 requires `import` commands to be the very first commands in a file, so the
-- header comment above forces this file to be self-contained (no imports).  The Fibonacci
-- numbers are therefore defined here directly, with the standard convention
-- `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

namespace Math

/-- The Fibonacci numbers, valued in `ℤ`: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`. -/

theorem cassini (n : Nat) : fib n * fib (n + 2) - fib (n + 1) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
      have hrec3 : fib (k + 3) = fib (k + 1) + fib (k + 2) := rfl
      have hrec2 : fib (k + 2) = fib k + fib (k + 1) := rfl
      have hpow : ((-1 : Int)) ^ (k + 2) = -((-1 : Int) ^ (k + 1)) := by
        rw [Int.pow_succ]
        grind
      rw [hrec3, hpow, ← ih, hrec2]
      grind

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

