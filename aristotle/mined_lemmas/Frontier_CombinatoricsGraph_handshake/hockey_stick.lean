import Mathlib
open Finset
namespace Frontier.CombinatoricsGraph

theorem hockey_stick (n k : ℕ) : ∑ i ∈ range (n+1), i.choose k = (n+1).choose (k+1) := by
  induction n with
  | zero => simp [Nat.choose_succ_succ]
  | succ n ih => rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ (n+1) k, Nat.add_comm]
end Frontier.CombinatoricsGraph

