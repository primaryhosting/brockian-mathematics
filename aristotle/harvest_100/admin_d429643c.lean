/-!
# Cassini 10
Category: Pure Mathematics
Target: Math.cassini_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
(This file carries the required header comment, which must precede any `import`,
so the development here is self-contained; `Math.fib` is shown to agree with
Mathlib's `Nat.fib` in `RequestProject.Cassini10Mathlib`.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 10`: `F(9) · F(11) − F(10)² = (−1)^10`,
stated over the integers. -/
theorem cassini_10 :
    (fib 9 : Int) * (fib 11 : Int) - (fib 10 : Int) ^ 2 = (-1) ^ 10 := by
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

import Mathlib
import RequestProject.Cassini10

/-!
# Cassini 10, Mathlib form

`Math.fib` agrees with Mathlib's `Nat.fib`, and Cassini's identity at `n = 10`
holds in the form `Nat.fib 9 * Nat.fib 11 - Nat.fib 10 ^ 2 = (-1) ^ 10` over `ℤ`.
-/

namespace Math

theorem fib_eq_natFib (n : ℕ) : fib n = Nat.fib n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) =>
      rw [fib, Nat.fib_add_two, ih n (by omega), ih (n + 1) (by omega)]

/-- Cassini's identity at `n = 10`, phrased with Mathlib's `Nat.fib`. -/
theorem cassini_10_natFib :
    (Nat.fib 9 : ℤ) * (Nat.fib 11 : ℤ) - (Nat.fib 10 : ℤ) ^ 2 = (-1) ^ 10 := by
  simpa [fib_eq_natFib] using cassini_10

end Math

