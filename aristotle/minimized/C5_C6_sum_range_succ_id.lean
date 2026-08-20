import Mathlib
open Finset
namespace C5.C6

/-- Gauss' summation formula, in the doubled form `2 * ∑_{i<n+1} i = n(n+1)`.
See `Finset.sum_range_id_mul_two` in Mathlib. -/

theorem sum_range_succ_id (n : ℕ) : 2 * ∑ i ∈ range (n+1), i = n*(n+1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

/-- Every binomial coefficient `n.choose k` is at most `2 ^ n`
(`Nat.choose_le_two_pow` / sum of a row of Pascal's triangle). -/
