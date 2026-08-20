import Mathlib
import RequestProject.Cassini7

/-!
# Cassini 7, in terms of Mathlib's `Nat.fib`

This companion file identifies the locally defined `Math.fib` with Mathlib's `Nat.fib`
and restates Cassini's identity at `n = 7` using `Nat.fib`.
-/

namespace Math

/-- The local Fibonacci function agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n : ℕ, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 7`, stated with Mathlib's `Nat.fib`:
`F(6) * F(8) - F(7)^2 = (-1)^7`. -/
theorem cassini_7_nat_fib :
    (Nat.fib 6 : ℤ) * (Nat.fib 8 : ℤ) - (Nat.fib 7 : ℤ) ^ 2 = (-1) ^ 7 := by
  simpa [fib_eq_nat_fib] using Math.cassini_7

end Math

/-!
# Cassini 7
Category: Pure Mathematics
Target: Math.cassini_7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.

(Defined here rather than using `Nat.fib` because Lean requires `import` commands to precede
any module documentation comment, and this file must begin with the header above.  The file
`RequestProject.Cassini7Mathlib` proves `Math.fib = Nat.fib` and restates the identity in
terms of Mathlib's `Nat.fib`.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 7`: `F(6) * F(8) - F(7)^2 = (-1)^7`. -/
theorem cassini_7 :
    (fib 6 : Int) * (fib 8 : Int) - (fib 7 : Int) ^ 2 = (-1) ^ 7 := by
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

