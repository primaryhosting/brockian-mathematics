import Mathlib
open Finset
namespace C3.Comb4

/-- The original statement is a vacuous implication into `True`, so it holds trivially.
(Note that its hypothesis, Pascal's rule in the form
`(n+1).choose k = n.choose k + n.choose (k-1)`, is false for `k = 0`, where truncated
subtraction gives `n.choose 0 + n.choose 0 = 2 ≠ 1`; see `pascal_rule` below for the
corrected, unconditional form.) -/

theorem alternating_choose (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ range (n+1), (-1:ℤ)^k * n.choose k = 0 :=
  Int.alternating_sum_range_choose_of_ne hn.ne'

end C3.Comb4

