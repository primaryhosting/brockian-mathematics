/-!
# Cassini 2
Category: Pure Mathematics
Target: Math.cassini_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires every `import` command to appear at the very
beginning of a file, before any comment or docstring.  Since the requested header
comment must be the first thing in this file, this module is kept self-contained
and import-free.  The companion module `RequestProject.CassiniMathlib` imports
Mathlib, identifies the Fibonacci function defined below with `Nat.fib`, and
restates Cassini's identity at `n = 2` in Mathlib terms.
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | (n + 2) => fib n + fib (n + 1)

/-- Cassini's identity at `n = 2`: `F(1) * F(3) - F(2)^2 = (-1)^2`, stated over `ℤ`. -/
theorem cassini_2 :
    (fib 1 : Int) * (fib 3 : Int) - (fib 2 : Int) ^ 2 = (-1 : Int) ^ 2 := by
  decide

end Math

import Mathlib
import RequestProject.Main

/-!
# Cassini 2, in Mathlib terms

This module identifies `Math.fib` with Mathlib's `Nat.fib` and restates Cassini's
identity at `n = 2` using `Nat.fib`.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/
theorem fib_eq_natFib : ∀ n : Nat, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | (n + 2) => by
      rw [Math.fib, Nat.fib_add_two, fib_eq_natFib n, fib_eq_natFib (n + 1)]

/-- Cassini's identity at `n = 2` for Mathlib's `Nat.fib`:
`F(1) * F(3) - F(2)^2 = (-1)^2`. -/
theorem cassini_2_natFib :
    (Nat.fib 1 : ℤ) * (Nat.fib 3 : ℤ) - (Nat.fib 2 : ℤ) ^ 2 = (-1 : ℤ) ^ 2 := by
  simpa [fib_eq_natFib] using Math.cassini_2

end Math

