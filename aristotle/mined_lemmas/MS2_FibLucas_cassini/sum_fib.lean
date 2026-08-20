import Mathlib
namespace MS2.FibLucas

/-- Cassini's identity. The statement is cast to `ℤ`, since `(-1)^n` does not
make sense in `ℕ`. -/

theorem sum_fib (n : ℕ) : ∑ i ∈ Finset.range n, Nat.fib i = Nat.fib (n+1) - 1 := by
  rw [Nat.fib_succ_eq_succ_sum]
  omega

