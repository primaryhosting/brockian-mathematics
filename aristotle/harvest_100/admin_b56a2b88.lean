/-!
# Cassini 5
Category: Pure Mathematics
Target: Math.cassini_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean requires `import` commands to be the very first
commands in a file, so this file (which must begin with the header comment
above) is written without imports, using a local copy `Math.fib` of the
Fibonacci sequence.  The companion file `RequestProject/MathMathlib.lean`
imports Mathlib, proves `Math.fib = Nat.fib`, and restates Cassini's identity
directly in terms of `Nat.fib`.
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`,
`fib (n + 2) = fib n + fib (n + 1)`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 5`: `F(4) · F(6) − F(5)² = (−1)^5`,
stated over the integers. -/
theorem cassini_5 :
    (fib 4 : Int) * (fib 6 : Int) - (fib 5 : Int) ^ 2 = (-1) ^ 5 := by
  decide

end Math

import Mathlib
import RequestProject.Math

/-!
# Cassini 5, Mathlib version

This companion file connects the self-contained development in
`RequestProject/Math.lean` with Mathlib's `Nat.fib`, and restates Cassini's
identity at `n = 5` in Mathlib terms.
-/

namespace Math

/-- The local Fibonacci sequence agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n : ℕ, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 5`, stated with Mathlib's `Nat.fib`:
`F(4) · F(6) − F(5)² = (−1)^5`. -/
theorem cassini_5_nat_fib :
    (Nat.fib 4 : ℤ) * (Nat.fib 6 : ℤ) - (Nat.fib 5 : ℤ) ^ 2 = (-1) ^ 5 := by
  simp only [← fib_eq_nat_fib]
  exact cassini_5

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

