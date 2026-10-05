/-!
# Cassini 4
Category: Pure Mathematics
Target: Math.cassini_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.

(Defined here rather than using `Nat.fib`, since Lean requires `import` commands to precede
every other command in a file, and this file must begin with the header comment above.
The file `RequestProject/Cassini4Mathlib.lean` proves `Math.fib = Nat.fib` and restates
Cassini's identity in terms of Mathlib's `Nat.fib`.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 4`: `F 3 * F 5 - F 4 ^ 2 = (-1) ^ 4`, over the integers. -/
theorem cassini_4 :
    (fib 3 : Int) * (fib 5 : Int) - (fib 4 : Int) ^ 2 = (-1) ^ 4 := by
  decide

end Math

import Mathlib
import RequestProject.Cassini4

/-!
# Cassini 4, in terms of Mathlib's `Nat.fib`

This companion file relates the self-contained `Math.fib` of `RequestProject/Cassini4.lean`
to Mathlib's `Nat.fib`, and restates the `n = 4` case of Cassini's identity accordingly.
-/

namespace Math

/-- The locally defined `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n : ℕ, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 4`, stated with Mathlib's `Nat.fib`:
`F 3 * F 5 - F 4 ^ 2 = (-1) ^ 4`. -/
theorem cassini_4_natFib :
    (Nat.fib 3 : ℤ) * (Nat.fib 5 : ℤ) - (Nat.fib 4 : ℤ) ^ 2 = (-1) ^ 4 := by
  simpa [fib_eq_nat_fib] using cassini_4

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

