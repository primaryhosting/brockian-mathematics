/-!
# Cassini 4
Category: Pure Mathematics
Target: Math.cassini_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.

(Defined here rather than using `Nat.fib` because the required file header must be the very
first thing in the file, and Lean forbids any `import` after a comment at the start of a file.
This definition agrees with `Nat.fib` by construction.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

@[simp] theorem fib_three : fib 3 = 2 := rfl
@[simp] theorem fib_four : fib 4 = 3 := rfl
@[simp] theorem fib_five : fib 5 = 5 := rfl

/-- Cassini's identity at `n = 4`: `F(3) * F(5) - F(4)^2 = (-1)^4`. -/
theorem cassini_4 :
    (fib 3 : Int) * (fib 5 : Int) - (fib 4 : Int) ^ 2 = (-1 : Int) ^ 4 := by
  decide

end Math

import Mathlib
import RequestProject.Cassini4

/-!
# Cassini 4 (Mathlib link)

This auxiliary file connects `Math.fib` with Mathlib's `Nat.fib` and restates Cassini's
identity at `n = 4` in terms of `Nat.fib`.
-/

namespace Math

theorem fib_eq_natFib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_natFib n, fib_eq_natFib (n + 1)]

/-- Cassini's identity at `n = 4`, stated with Mathlib's `Nat.fib`. -/
theorem cassini_4_natFib :
    (Nat.fib 3 : ℤ) * (Nat.fib 5 : ℤ) - (Nat.fib 4 : ℤ) ^ 2 = (-1 : ℤ) ^ 4 := by
  simpa [fib_eq_natFib] using cassini_4

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

