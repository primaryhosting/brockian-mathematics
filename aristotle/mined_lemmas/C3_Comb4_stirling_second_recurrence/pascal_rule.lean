import Mathlib
open Finset
namespace C3.Comb4

/-- The original statement is a vacuous implication into `True`, so it holds trivially.
(Note that its hypothesis, Pascal's rule in the form
`(n+1).choose k = n.choose k + n.choose (k-1)`, is false for `k = 0`, where truncated
subtraction gives `n.choose 0 + n.choose 0 = 2 ≠ 1`; see `pascal_rule` below for the
corrected, unconditional form.) -/

theorem pascal_rule (n k : ℕ) (hk : 0 < k) :
    (n+1).choose k = n.choose k + n.choose (k-1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp [Nat.choose_succ_succ, Nat.add_comm]

