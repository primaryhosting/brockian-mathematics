import Mathlib
import RequestProject.Cassini4

/-!
# Cassini 4, phrased with Mathlib's `Nat.fib`
-/

namespace Math

/-- The locally defined Fibonacci sequence agrees with Mathlib's `Nat.fib`. -/
theorem F_eq_fib : ∀ n, F n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [F, F_eq_fib n, F_eq_fib (n + 1), Nat.fib_add_two]

/-- Cassini's identity at `n = 4`, with Mathlib's `Nat.fib`:
`fib 3 * fib 5 - fib 4 ^ 2 = (-1) ^ 4`. -/
theorem cassini_4_fib :
    (Nat.fib 3 : ℤ) * (Nat.fib 5 : ℤ) - (Nat.fib 4 : ℤ) ^ 2 = (-1 : ℤ) ^ 4 := by
  simpa [F_eq_fib] using cassini_4

end Math

/-!
# Cassini 4
Category: Pure Mathematics
Target: Math.cassini_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

(This file is kept import-free so that the required header comment can be the very first
thing in the file; Lean does not allow a module doc comment to precede an `import`.
The Mathlib version of the statement, phrased with `Nat.fib`, is in `Cassini4Fib.lean`.) -/
def F : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => F n + F (n + 1)

/-- Cassini's identity at `n = 4`: `F 3 * F 5 - F 4 ^ 2 = (-1) ^ 4`. -/
theorem cassini_4 : (F 3 : Int) * (F 5 : Int) - (F 4 : Int) ^ 2 = (-1 : Int) ^ 4 := by
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

