/-!
# Cassini 5
Category: Pure Mathematics
Target: Math.cassini_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file structure: Lean 4 requires every `import` command to appear at the very
beginning of a file, before any other command (including a module docstring).  Since
this file is required to begin with the header block above, it cannot contain imports,
so it is stated self-contained over Lean core: the Fibonacci sequence is defined here
as `Math.fib`.  The companion file `RequestProject/Cassini5Mathlib.lean` imports
Mathlib, proves `Math.fib = Nat.fib`, and restates the result in terms of Mathlib's
`Nat.fib`.
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 5`: `F(4) * F(6) - F(5)^2 = (-1)^5`. -/
theorem cassini_5 :
    (fib 4 : Int) * (fib 6 : Int) - (fib 5 : Int) ^ 2 = (-1) ^ 5 := by
  decide

end Math

import Mathlib
import RequestProject.Cassini5

/-!
# Cassini 5, in terms of Mathlib's `Nat.fib`

This companion file connects the self-contained statement `Math.cassini_5` (proved in
`RequestProject/Cassini5.lean`) with Mathlib's Fibonacci function `Nat.fib`.
-/

namespace Math

/-- The locally defined `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_natFib : ∀ n : ℕ, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_natFib n, fib_eq_natFib (n + 1)]

/-- Cassini's identity at `n = 5`, stated with Mathlib's `Nat.fib`:
`F(4) * F(6) - F(5)^2 = (-1)^5`. -/
theorem cassini_5_natFib :
    (Nat.fib 4 : ℤ) * (Nat.fib 6 : ℤ) - (Nat.fib 5 : ℤ) ^ 2 = (-1) ^ 5 := by
  simpa [fib_eq_natFib] using cassini_5

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

