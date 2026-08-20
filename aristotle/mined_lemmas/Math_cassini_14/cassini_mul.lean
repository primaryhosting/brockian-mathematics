/-
Supplement to `RequestProject/Cassini14.lean`: identifies the Fibonacci sequence
`Math.fib` used there with Mathlib's `Nat.fib`, and restates Cassini 14 for `Nat.fib`.
-/
import Mathlib
import RequestProject.Cassini14

namespace Math


theorem cassini_mul (n : Nat) :
    fib (n + 1) * fib (n + 3) - fib (n + 2) * fib (n + 2) = (-1 : Int) ^ (n + 2) := by
  induction n with
  | zero => decide
  | succ k ih =>
      have h3 : fib (k + 3) = fib (k + 1) + fib (k + 2) := fib_add_two (k + 1)
      have h4 : fib (k + 4) = fib (k + 2) + fib (k + 3) := fib_add_two (k + 2)
      have hp : ((-1 : Int)) ^ (k + 3) = -((-1 : Int)) ^ (k + 2) := by
        simp [Int.pow_succ]
      rw [show k + 1 + 1 = k + 2 from rfl, show k + 1 + 2 = k + 3 from rfl,
        show k + 1 + 3 = k + 4 from rfl, hp, h4, h3]
      rw [h3] at ih
      generalize ((-1 : Int)) ^ (k + 2) = c at ih
      generalize fib (k + 1) = a at ih ⊢
      generalize fib (k + 2) = b at ih ⊢
      grind

/-- Cassini's identity: `F (n + 1) * F (n + 3) - F (n + 2) ^ 2 = (-1) ^ (n + 2)`. -/
