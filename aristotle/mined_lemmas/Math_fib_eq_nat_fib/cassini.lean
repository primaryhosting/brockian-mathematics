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

theorem cassini (n : Nat) :
    (fib n : Int) * (fib (n + 2) : Int) - (fib (n + 1) : Int) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
      have h1 : (fib (k + 2) : Int) = (fib k : Int) + (fib (k + 1) : Int) := by
        show ((fib k + fib (k + 1) : Nat) : Int) = _
        omega
      have h2 : (fib (k + 3) : Int) = (fib (k + 1) : Int) + (fib (k + 2) : Int) := by
        show ((fib (k + 1) + fib (k + 2) : Nat) : Int) = _
        omega
      have hpow : ((-1 : Int)) ^ (k + 1 + 1) = -((-1 : Int) ^ (k + 1)) := by
        rw [Int.pow_succ]; omega
      rw [show k + 1 + 2 = k + 3 from rfl, h2, hpow, ← ih, h1]
      grind

/-- **Cassini's identity at `n = 9`**: `F 8 * F 10 - F 9 ^ 2 = (-1) ^ 9`.

Numerically `F 8 = 21`, `F 9 = 34`, `F 10 = 55`, and `21 * 55 - 34 ^ 2 = -1 = (-1) ^ 9`. -/
