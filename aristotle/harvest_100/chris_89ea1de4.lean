/-!
# Cassini 2
Category: Pure Mathematics
Target: Math.cassini_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean requires `import` commands to precede every other command in a file,
so this module is kept import-free in order to begin with the header comment
exactly as requested. The Fibonacci sequence is therefore defined locally here;
the companion module `RequestProject.CassiniMathlib` imports Mathlib, proves
`Math.fib = Nat.fib`, and restates Cassini's identity with Mathlib's `Nat.fib`.
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
This agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_nat_fib`). -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 2`: `F(1) · F(3) − F(2)² = (−1)²`, over the integers. -/
theorem cassini_2 :
    (fib 1 : Int) * (fib 3 : Int) - (fib 2 : Int) ^ 2 = (-1) ^ 2 := by
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
import RequestProject.Math

/-!
# Cassini 2, stated with Mathlib's `Nat.fib`

This module links the import-free development in `RequestProject.Math` with
Mathlib's Fibonacci sequence `Nat.fib`.
-/

namespace Math

/-- The locally defined `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 2` for Mathlib's `Nat.fib`:
`F(1) · F(3) − F(2)² = (−1)²`. -/
theorem cassini_2_nat_fib :
    (Nat.fib 1 : ℤ) * (Nat.fib 3 : ℤ) - (Nat.fib 2 : ℤ) ^ 2 = (-1) ^ 2 := by
  norm_num [Nat.fib]

end Math

