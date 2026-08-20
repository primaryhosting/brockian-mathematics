import Mathlib
namespace MS2.FibLucas

/-- Cassini's identity. The statement is cast to `ℤ`, since `(-1)^n` does not
make sense in `ℕ`. -/

theorem cassini (n : ℕ) :
    (Nat.fib (n+2) : ℤ) * (Nat.fib n : ℤ) + (-1)^n = (Nat.fib (n+1) : ℤ)^2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : (Nat.fib (k + 1 + 2) : ℤ) = (Nat.fib (k + 1) : ℤ) + (Nat.fib (k + 2) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast (R := ℤ)) (Nat.fib_add_two (n := k + 1))
    have h2 : (Nat.fib (k + 2) : ℤ) = (Nat.fib k : ℤ) + (Nat.fib (k + 1) : ℤ) := by
      exact_mod_cast congrArg (Nat.cast (R := ℤ)) (Nat.fib_add_two (n := k))
    rw [h1, h2]
    rw [h2] at ih
    ring_nf
    ring_nf at ih
    linarith [ih]

