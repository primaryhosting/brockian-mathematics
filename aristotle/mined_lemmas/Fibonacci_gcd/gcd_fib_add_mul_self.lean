/-!
# Gcd
Category: Fibonacci
Target: Fibonacci.gcd
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the file layout: Lean does not allow any command (including a module
docstring `/-! ... -/`) to precede the `import` lines of a file, so this file,
which must begin with the header comment above, carries no imports and develops
the statement from the Lean core library alone.  The companion file
`RequestProject/GcdMathlib.lean` imports Mathlib, checks that the Fibonacci
function defined here agrees with Mathlib's `Nat.fib`, and records the literal
Mathlib statement `Nat.fib (Nat.gcd m n) = Nat.gcd (Nat.fib m) (Nat.fib n)`
(proved via `Nat.fib_gcd`).
-/

namespace Fibonacci

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`.
This is the same function as Mathlib's `Nat.fib`. -/

theorem gcd_fib_add_mul_self (m n k : Nat) :
    Nat.gcd (fib m) (fib (n + m * k)) = Nat.gcd (fib m) (fib n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : n + m * (k + 1) = (n + m * k) + m := by
      rw [Nat.mul_succ]; omega
    rw [h, gcd_fib_add_self, ih]

/-- **Fibonacci-gcd**: `fib (gcd m n) = gcd (fib m) (fib n)` for all naturals `m n`. -/
