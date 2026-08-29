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

theorem nat_fib_cassini (n : ℕ) :
    (Nat.fib n : ℤ) * (Nat.fib (n + 2) : ℤ) - (Nat.fib (n + 1) : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have h1 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
        rw [Nat.fib_add_two]; push_cast; ring
      have h2 : (Nat.fib (k + 3) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
        rw [show k + 3 = (k + 1) + 2 from rfl, Nat.fib_add_two]; push_cast; ring
      have hpow : ((-1 : ℤ)) ^ (k + 1 + 1) = -((-1 : ℤ) ^ (k + 1)) := by
        rw [pow_succ]; ring
      rw [show k + 1 + 2 = k + 3 from rfl, h2, hpow, ← ih, h1]
      ring

/-- Cassini's identity at `n = 9`, stated with Mathlib's `Nat.fib`. -/
