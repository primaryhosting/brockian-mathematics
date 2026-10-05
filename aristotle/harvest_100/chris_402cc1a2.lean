/-!
# Cassini 9
Category: Pure Mathematics
Target: Math.cassini_9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Fibonacci sequence, `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
(Defined here rather than taken from Mathlib because the required file header is a module
docstring, which Lean requires to precede any `import` command; the file
`RequestProject/CassiniMathlib.lean` proves this agrees with `Nat.fib` and restates the
result in Mathlib terms.) -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Cassini's identity at `n = 9`: `F(8) * F(10) - F(9)^2 = (-1)^9`, stated over `ℤ`. -/
theorem cassini_9 :
    (fib 8 : Int) * (fib 10 : Int) - (fib 9 : Int) ^ 2 = (-1) ^ 9 := by
  decide

end Math

import Mathlib
import RequestProject.Main

/-!
# Cassini 9, in Mathlib terms

This file connects the self-contained `Math.fib` of `RequestProject/Main.lean` with
Mathlib's `Nat.fib`, and restates Cassini's identity at `n = 9` for `Nat.fib`.
-/

namespace Math

/-- The locally defined `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_nat_fib : ∀ n, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- Cassini's identity at `n = 9` for Mathlib's `Nat.fib`:
`F(8) * F(10) - F(9)^2 = (-1)^9`. -/
theorem cassini_9_nat_fib :
    (Nat.fib 8 : ℤ) * (Nat.fib 10 : ℤ) - (Nat.fib 9 : ℤ) ^ 2 = (-1) ^ 9 := by
  simpa [fib_eq_nat_fib] using cassini_9

end Math

