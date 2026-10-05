import Mathlib
import RequestProject.Math

/-!
# Cassini 9 — Mathlib restatement

`Math.fib` agrees with Mathlib's `Nat.fib`, and Cassini's identity at `n = 9`
holds for `Nat.fib` as well.  No general Cassini identity was found in the Mathlib version
pinned by this project (searches for `fib`-based Cassini/Catalan identities returned nothing),
so the numeric instance is closed by kernel computation.
-/

namespace Math

theorem fib_eq_nat_fib : ∀ n : Nat, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1), Nat.add_comm]

/-- Cassini's identity at `n = 9` for Mathlib's `Nat.fib`. -/
theorem cassini_9_nat_fib :
    (Nat.fib 8 : ℤ) * (Nat.fib 10 : ℤ) - (Nat.fib 9 : ℤ) ^ 2 = (-1) ^ 9 := by
  simpa [fib_eq_nat_fib] using cassini_9

end Math

/-!
# Cassini 9
Category: Pure Mathematics
Target: Math.cassini_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`.
(This file carries the required module-header comment, which Lean requires to precede
any `import` line; the identification of this sequence with Mathlib's `Nat.fib`, and the
Mathlib-flavoured restatement of the theorem below, are in `RequestProject.MathFib`.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- **Cassini's identity at `n = 9`**: `F 8 * F 10 - F 9 ^ 2 = (-1) ^ 9`,
i.e. `21 * 55 - 34 ^ 2 = -1`, over the integers. -/
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

