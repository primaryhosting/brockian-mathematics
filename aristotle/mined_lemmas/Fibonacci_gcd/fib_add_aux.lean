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

theorem fib_add_aux (m k : Nat) :
    fib (m + k + 1) = fib m * fib k + fib (m + 1) * fib (k + 1) ∧
      fib (m + k + 2) = fib m * fib (k + 1) + fib (m + 1) * fib (k + 2) := by
  induction k with
  | zero =>
    constructor
    · simp
    · rw [fib_add_two m]
      simp [fib_add_two 0]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hstep : fib (m + k + 3) = fib (m + k + 1) + fib (m + k + 2) := fib_add_two (m + k + 1)
    have hk : fib (k + 3) = fib (k + 1) + fib (k + 2) := fib_add_two (k + 1)
    constructor
    · show fib (m + k + 2) = _
      rw [ih2]
    · show fib (m + k + 3) = fib m * fib (k + 2) + fib (m + 1) * fib (k + 3)
      rw [hstep, ih1, ih2, hk, fib_add_two k]
      simp [Nat.mul_add]
      omega

/-- The Fibonacci addition formula. -/
