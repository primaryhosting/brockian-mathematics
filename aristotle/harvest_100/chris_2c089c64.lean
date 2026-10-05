/-!
# Cassini 10
Category: Pure Mathematics
Target: Math.cassini_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.
(Defined here rather than imported, since the required file header must be the
very first thing in the file, which rules out an `import` line.) -/
def F : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => F n + F (n + 1)

/-- Cassini's identity at `n = 10`: `F 9 * F 11 - (F 10)^2 = (-1)^10`, over `ℤ`. -/
theorem cassini_10 : (F 9 : Int) * (F 11 : Int) - (F 10 : Int) ^ 2 = (-1) ^ 10 := by
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
Companion file: identifies the locally defined Fibonacci sequence `Math.F` with
Mathlib's `Nat.fib`, and restates Cassini's identity at `n = 10` in those terms.
-/

namespace Math

theorem F_eq_fib (n : Nat) : F n = Nat.fib n := by
  induction n using F.induct with
  | case1 => rfl
  | case2 => rfl
  | case3 n ih1 ih2 =>
      rw [F, ih1, ih2, Nat.fib_add_two, Nat.add_comm]

/-- Cassini's identity at `n = 10`, stated with Mathlib's `Nat.fib`. -/
theorem cassini_10_fib :
    (Nat.fib 9 : Int) * (Nat.fib 11 : Int) - (Nat.fib 10 : Int) ^ 2 = (-1) ^ 10 := by
  simpa [F_eq_fib] using cassini_10

end Math

