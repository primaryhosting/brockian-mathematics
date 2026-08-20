import Mathlib
open Finset
namespace C6.C7

/-- `6 * ∑_{i=0}^{n} i^2 = n(n+1)(2n+1)`, by induction on `n`. -/

theorem sum_sq_formula (n : ℕ) : 6 * ∑ i ∈ range (n+1), i^2 = n*(n+1)*(2*n+1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, Nat.mul_add, ih]; ring

/-- `C(n,k) * k! * (n-k)! = n!` for `k ≤ n`
(`Nat.choose_mul_factorial_mul_factorial` in Mathlib). -/
