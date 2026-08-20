/-!
# Cassini 8
Category: Pure Mathematics
Target: Math.cassini_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean requires `import` commands to precede every other command in a file,
including module doc comments, so this file (whose first token must be the header
above) is kept self-contained and uses only Lean core. The Fibonacci numbers are
therefore defined here; `Math.fib` agrees with Mathlib's `Nat.fib`
(`fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`).
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- `F(7) = 13`, `F(8) = 21`, `F(9) = 34`. -/
theorem fib_values : fib 7 = 13 ∧ fib 8 = 21 ∧ fib 9 = 34 := by
  refine ⟨rfl, rfl, rfl⟩

/-- Cassini's identity at `n = 8`: `F(7) * F(9) - F(8)^2 = (-1)^8`. -/
theorem cassini_8 :
    (fib 7 : Int) * (fib 9 : Int) - (fib 8 : Int) ^ 2 = (-1 : Int) ^ 8 := by
  decide

end Math

import Mathlib
import RequestProject.Cassini8

/-!
# Cassini 8, cross-checked against Mathlib

The main statement `Math.cassini_8` lives in `RequestProject/Cassini8.lean`, which must be
self-contained (its first token is a prescribed header comment, and Lean requires imports to
come first in a file). Here we check that the Fibonacci sequence used there coincides with
Mathlib's `Nat.fib`, and restate Cassini's identity at `n = 8` in terms of `Nat.fib`.
-/

namespace Math

/-- The locally defined `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 8`, stated with Mathlib's `Nat.fib`. -/
theorem cassini_8_nat_fib :
    (Nat.fib 7 : ℤ) * (Nat.fib 9 : ℤ) - (Nat.fib 8 : ℤ) ^ 2 = (-1 : ℤ) ^ 8 := by
  simpa [fib_eq_nat_fib] using cassini_8

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

