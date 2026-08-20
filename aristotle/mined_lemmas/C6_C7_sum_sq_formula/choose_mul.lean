import Mathlib
open Finset
namespace C6.C7

/-- `6 * ∑_{i=0}^{n} i^2 = n(n+1)(2n+1)`, by induction on `n`. -/

theorem choose_mul (n k : ℕ) (h : k ≤ n) :
    n.choose k * k.factorial * (n-k).factorial = n.factorial :=
  Nat.choose_mul_factorial_mul_factorial h

/-- The sum of the squares of a row of Pascal's triangle is a central binomial
coefficient (`Nat.sum_range_choose_sq`, a consequence of Vandermonde's identity). -/
