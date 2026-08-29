import Mathlib
import RequestProject.Math

/-!
# Cassini's identity: companion file

`RequestProject.Math` is required to begin with a fixed header comment, hence it cannot
contain an `import` command and its Fibonacci sequence `Math.fib` is defined from scratch.
Here we import Mathlib and check that `Math.fib` is Mathlib's `Nat.fib`, restate
`Math.cassini_9` in terms of `Nat.fib`, and prove the general Cassini identity.

A search of this Mathlib version turned up no lemma stating Cassini's identity for
`Nat.fib` (only related identities such as `Nat.fib_add_two_sub_fib_add_one` and
`Nat.fib_two_mul_add_one`), so the general statement is proved here by induction.
-/

namespace Math

/-- `Math.fib` agrees with Mathlib's `Nat.fib`. -/

theorem fib_eq_nat_fib : ∀ n : ℕ, Math.fib n = Nat.fib n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      rw [Math.fib, Nat.fib_add_two, fib_eq_nat_fib n, fib_eq_nat_fib (n + 1)]

/-- **Cassini's identity**: `F n * F (n+2) - F (n+1) ^ 2 = (-1) ^ (n+1)` over `ℤ`. -/
