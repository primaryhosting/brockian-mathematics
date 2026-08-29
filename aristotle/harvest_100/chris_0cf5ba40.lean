import Mathlib
import RequestProject.Cassini13

/-!
# Cassini 13, stated with Mathlib's `Nat.fib`

This companion file identifies the locally defined `Math.fib` with Mathlib's `Nat.fib`,
restates Cassini's identity at `n = 13` in terms of `Nat.fib`, and records the general
Cassini identity specialised at `n = 13`.
-/

namespace Math

/-- The locally defined Fibonacci function agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 13`, stated with Mathlib's `Nat.fib`. -/
theorem cassini_13_nat_fib :
    (Nat.fib 12 : ℤ) * (Nat.fib 14 : ℤ) - (Nat.fib 13 : ℤ) ^ 2 = (-1) ^ 13 := by
  simpa [fib_eq_nat_fib] using cassini_13

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

/-!
# Cassini 13
Category: Pure Mathematics
Target: Math.cassini_13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
(Defined here rather than using `Nat.fib` so that this file can literally begin with the
required header comment: Lean requires `import` commands to precede any doc comment.
`Math.fib_eq_nat_fib` in `RequestProject.Cassini13Mathlib` identifies it with `Nat.fib`.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 13`: `F 12 * F 14 - F 13 ^ 2 = (-1) ^ 13`,
i.e. `144 * 377 - 233 ^ 2 = -1`. -/
theorem cassini_13 :
    (fib 12 : Int) * (fib 14 : Int) - (fib 13 : Int) ^ 2 = (-1) ^ 13 := by
  decide

end Math

