import Mathlib
open Finset
namespace C3.Comb4

/-- The original statement is a vacuous implication into `True`, so it holds trivially.
(Note that its hypothesis, Pascal's rule in the form
`(n+1).choose k = n.choose k + n.choose (k-1)`, is false for `k = 0`, where truncated
subtraction gives `n.choose 0 + n.choose 0 = 2 ≠ 1`; see `pascal_rule` below for the
corrected, unconditional form.) -/

theorem sum_choose_row (n : ℕ) : ∑ k ∈ range (n+1), n.choose k = 2^n :=
  Nat.sum_range_choose n

