/-
# Cassini 3
Category: Pure Mathematics
Target: Math.cassini_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is written as a plain block comment `/- ... -/` rather than a
-- module docstring `/-! ... -/`, because Lean 4 requires `import` commands to precede
-- every command in a file, and a module docstring counts as a command.)

import Mathlib

namespace Math

/-- **Cassini's identity at `n = 3`**: `F(2) · F(4) − F(3)² = (−1)³`,
stated over `ℤ` (with `F` the Fibonacci sequence `Nat.fib`).

Numerically: `F(2) = 1`, `F(3) = 2`, `F(4) = 3`, so `1 · 3 − 2² = −1 = (−1)³`.

Mathlib does not, in this version, provide a general Cassini identity lemma that
closes this goal: `exact?` finds nothing for the general statement
`F(n+2)·F(n) − F(n+1)² = (−1)^(n+1)`. Since all indices here are numerals, the
identity is a finite computation, discharged by `decide`. -/

theorem cassini_3 :
    (Nat.fib 2 : ℤ) * (Nat.fib 4 : ℤ) - (Nat.fib 3 : ℤ) ^ 2 = (-1) ^ 3 := by
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

