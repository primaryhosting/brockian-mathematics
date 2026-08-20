/-!
# Cassini 5
Category: Pure Mathematics
Target: Math.cassini_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.

(This file is required to begin with the header comment above, and Lean only accepts
`import` commands at the very start of a file, so the file is self-contained in core Lean.
`Math.fib` agrees with Mathlib's `Nat.fib`; see `RequestProject/Cassini5Mathlib.lean`,
where the same identity is also stated and proved for `Nat.fib`.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 5`: `F 4 * F 6 - F 5 ^ 2 = (-1) ^ 5`,
i.e. `3 * 8 - 5 ^ 2 = -1`, stated over the integers. -/
theorem cassini_5 : (fib 4 : Int) * (fib 6 : Int) - (fib 5 : Int) ^ 2 = (-1 : Int) ^ 5 := by
  decide

end Math

import Mathlib
import RequestProject.Cassini5

/-!
# Cassini 5, with Mathlib's `Nat.fib`

This companion file restates Cassini's identity at `n = 5` using Mathlib's `Nat.fib`,
and records that `Math.fib` agrees with `Nat.fib`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n : ℕ, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 5` for Mathlib's `Nat.fib`:
`F 4 * F 6 - F 5 ^ 2 = (-1) ^ 5`. -/
theorem cassini_5_natFib :
    (Nat.fib 4 : ℤ) * (Nat.fib 6 : ℤ) - (Nat.fib 5 : ℤ) ^ 2 = (-1 : ℤ) ^ 5 := by
  norm_num [Nat.fib]

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

