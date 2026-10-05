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

theorem fib_coprime_fib_succ (n : Nat) : Nat.Coprime (fib n) (fib (n + 1)) := by
  induction n with
  | zero => decide
  | succ k ih =>
    show Nat.gcd (fib (k + 1)) (fib (k + 2)) = 1
    rw [fib_add_two k, Nat.gcd_add_self_right]
    rw [Nat.gcd_comm]
    exact ih

