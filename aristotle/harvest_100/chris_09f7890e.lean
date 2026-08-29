/-!
# Cassini 15
Category: Pure Mathematics
Target: Math.cassini_15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
This agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_nat_fib` in `Cassini15Mathlib.lean`). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 15`: `F(14) * F(16) - F(15)^2 = (-1)^15`. -/
theorem cassini_15 :
    (fib 14 : Int) * (fib 16 : Int) - (fib 15 : Int) ^ 2 = (-1) ^ 15 := by
  decide

end Math

import Mathlib
import RequestProject.Cassini15

/-!
# Cassini 15, stated with Mathlib's `Nat.fib`

The target theorem `Math.cassini_15` lives in `Cassini15.lean`, whose required header comment
must be the very first thing in that file; since a module docstring cannot precede `import`
statements, that file is self-contained and uses its own `Math.fib`.  Here we check that
`Math.fib` really is Mathlib's `Nat.fib`, and restate Cassini's identity accordingly.
-/

namespace Math

theorem fib_eq_nat_fib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 15`, phrased with Mathlib's `Nat.fib`. -/
theorem cassini_15_nat_fib :
    (Nat.fib 14 : ℤ) * (Nat.fib 16 : ℤ) - (Nat.fib 15 : ℤ) ^ 2 = (-1) ^ 15 := by
  simpa [fib_eq_nat_fib] using cassini_15

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

