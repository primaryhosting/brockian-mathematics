import Mathlib
open Finset
namespace C6.C7

/-- `6 * ∑_{i=0}^{n} i^2 = n(n+1)(2n+1)`, by induction on `n`. -/

theorem sum_choose_two (n : ℕ) : ∑ k ∈ range (n+1), (n.choose k)^2 = (2*n).choose n :=
  Nat.sum_range_choose_sq n

end C6.C7

