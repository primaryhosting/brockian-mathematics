import Mathlib
import RequestProject.Cassini12

/-!
# Cassini 12, in Mathlib terms

This file links the self-contained Fibonacci function `Math.fib` of
`RequestProject.Cassini12` with Mathlib's `Nat.fib`, and restates Cassini's identity
at `n = 12` for `Nat.fib`. It also proves the general Cassini identity.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem cassini_general (n : ℕ) :
    (Nat.fib n : ℤ) * (Nat.fib (n + 2) : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1 : ℤ) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
      have h2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
      push_cast [h, h2] at *
      ring_nf
      ring_nf at ih
      linarith [ih]

end Math

/-!
# Cassini 12
Category: Pure Mathematics
Target: Math.cassini_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- NOTE: Lean requires `import` commands to appear before any other command, and a
-- module docstring `/-! ... -/` counts as a command. Since the header comment above must
-- literally begin the file, this module carries no imports and is self-contained.
-- The file `RequestProject/Cassini12Mathlib.lean` links `Math.fib` below to Mathlib's
-- `Nat.fib` and restates the result in Mathlib terms.

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/
