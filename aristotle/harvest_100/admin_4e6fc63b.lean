/-!
# Cassini 9
Category: Pure Mathematics
Target: Math.cassini_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, agreeing with `Nat.fib` from Mathlib
(`fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 9`: `F 8 * F 10 - F 9 ^ 2 = (-1) ^ 9`. -/
theorem cassini_9 :
    (fib 8 : Int) * (fib 10 : Int) - (fib 9 : Int) ^ 2 = (-1) ^ 9 := by
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
import RequestProject.Cassini9

/-!
# Cassini 9 — Mathlib bridge

`RequestProject/Cassini9.lean` must begin with a fixed module-doc header, and Lean
requires `import` lines to come first in a file, so that file is import-free and uses
its own `Math.fib`.  Here we import Mathlib and check that `Math.fib` agrees with
`Nat.fib`, and restate Cassini's identity at `n = 9` for `Nat.fib`.

The numeric statement is closed directly by the `norm_num` extension for Fibonacci
numbers (`Mathlib/Tactic/NormNum/NatFib.lean`); Mathlib has no general Cassini identity.
-/

namespace Math

theorem fib_eq_nat_fib : ∀ n : ℕ, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 9`, stated with Mathlib's `Nat.fib`. -/
theorem cassini_9_natFib :
    (Nat.fib 8 : ℤ) * (Nat.fib 10 : ℤ) - (Nat.fib 9 : ℤ) ^ 2 = (-1) ^ 9 := by
  norm_num

end Math

