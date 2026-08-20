/-!
# Cassini 11
Category: Pure Mathematics
Target: Math.cassini_11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
This agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_natFib` in `Cassini11Mathlib.lean`). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 11`: `F 10 * F 12 - F 11 ^ 2 = (-1) ^ 11`. -/
theorem cassini_11 :
    (fib 10 : Int) * (fib 12 : Int) - (fib 11 : Int) ^ 2 = (-1) ^ 11 := by
  decide

end Math

import Mathlib
import RequestProject.Cassini11

/-!
# Cassini 11, stated with Mathlib's `Nat.fib`

The main file `Cassini11.lean` must begin with a fixed header comment, which prevents it
from carrying an `import` line, so it defines the Fibonacci sequence from scratch.  Here we
check that this definition agrees with Mathlib's `Nat.fib`, and restate Cassini's identity
at `n = 11` in terms of `Nat.fib`.
-/

namespace Math

theorem fib_eq_natFib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_natFib n, fib_eq_natFib (n + 1)]

/-- Cassini's identity at `n = 11`, in terms of `Nat.fib`. -/
theorem cassini_11_natFib :
    (Nat.fib 10 : ℤ) * (Nat.fib 12 : ℤ) - (Nat.fib 11 : ℤ) ^ 2 = (-1) ^ 11 := by
  simpa [fib_eq_natFib] using cassini_11

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

