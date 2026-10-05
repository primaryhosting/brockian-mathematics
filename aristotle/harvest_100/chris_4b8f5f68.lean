/-!
# Cassini 8
Category: Pure Mathematics
Target: Math.cassini_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
This agrees with Mathlib's `Nat.fib` (see `Math.fib_eq_natFib` in `RequestProject/CassiniFib.lean`).
It is defined here rather than imported because this module must begin with the required
header comment, which Lean only permits in a file with no `import` lines. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity at `n = 8`**: `F 7 * F 9 - F 8 ^ 2 = (-1) ^ 8`,
i.e. `13 * 34 - 21 ^ 2 = 1`. -/
theorem cassini_8 :
    (fib 7 : Int) * (fib 9 : Int) - (fib 8 : Int) ^ 2 = (-1) ^ 8 := by
  decide

end Math

import Mathlib
import RequestProject.Math

/-!
# Cassini 8 — Mathlib `Nat.fib` version

Mathlib (as of this version) contains no Cassini identity lemma, so we prove the
`n = 8` instance directly and record that the locally defined `Math.fib` agrees
with Mathlib's `Nat.fib`.
-/

namespace Math

/-- The locally defined `Math.fib` coincides with Mathlib's `Nat.fib`. -/
theorem fib_eq_natFib : ∀ n : Nat, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_natFib n, fib_eq_natFib (n + 1)]

/-- **Cassini's identity at `n = 8`** stated with Mathlib's `Nat.fib`. -/
theorem cassini_8_natFib :
    (Nat.fib 7 : ℤ) * (Nat.fib 9 : ℤ) - (Nat.fib 8 : ℤ) ^ 2 = (-1) ^ 8 := by
  simpa [fib_eq_natFib] using cassini_8

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

