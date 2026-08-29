/-!
# Cassini 5
Category: Pure Mathematics
Target: Math.cassini_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file structure: Lean 4 requires every `import` command to appear at the very
beginning of a file, before any other command (including a module docstring).  Since
this file is required to begin with the header block above, it cannot contain imports,
so it is stated self-contained over Lean core: the Fibonacci sequence is defined here
as `Math.fib`.  The companion file `RequestProject/Cassini5Mathlib.lean` imports
Mathlib, proves `Math.fib = Nat.fib`, and restates the result in terms of Mathlib's
`Nat.fib`.
-/

namespace Math

/-- The Fibonacci sequence: `fib 0 = 0`, `fib 1 = 1`, `fib (n+2) = fib n + fib (n+1)`. -/

theorem fib_eq_natFib : ∀ n : ℕ, fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [fib, Nat.fib_add_two, fib_eq_natFib n, fib_eq_natFib (n + 1)]

/-- Cassini's identity at `n = 5`, stated with Mathlib's `Nat.fib`:
`F(4) * F(6) - F(5)^2 = (-1)^5`. -/
