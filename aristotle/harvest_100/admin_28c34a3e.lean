import Mathlib
import RequestProject.Cassini2

/-!
# Cassini 2 (Mathlib version)

Cassini's identity at `n = 2`, stated for Mathlib's `Nat.fib`, together with the
agreement of `Math.fib` and `Nat.fib`.
-/

namespace Math

/-- The Fibonacci function of `Cassini2.lean` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 2` for Mathlib's `Nat.fib`. -/
theorem cassini_2_nat_fib :
    (Nat.fib 1 : ℤ) * (Nat.fib 3 : ℤ) - (Nat.fib 2 : ℤ) ^ 2 = (-1 : ℤ) ^ 2 := by
  simp [← fib_eq_nat_fib, Math.fib]

end Math

/-!
# Cassini 2
Category: Pure Mathematics
Target: Math.cassini_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: this file must *begin* with the header comment above, and in Lean 4 no
-- `import` command may follow a module docstring, so the file is kept
-- import-free (it uses only the core `Init` prelude).  The companion file
-- `RequestProject/Cassini2Mathlib.lean` imports Mathlib and shows that the
-- Fibonacci function used here agrees with Mathlib's `Nat.fib`, and restates
-- Cassini's identity in terms of `Nat.fib`.

namespace Math

/-- The Fibonacci sequence: `F 0 = 0`, `F 1 = 1`, `F (n+2) = F n + F (n+1)`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 2`: `F 1 * F 3 - F 2 ^ 2 = (-1) ^ 2`. -/
theorem cassini_2 :
    (fib 1 : Int) * (fib 3 : Int) - (fib 2 : Int) ^ 2 = (-1 : Int) ^ 2 := by
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

