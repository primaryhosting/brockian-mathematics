import Mathlib
open Finset
namespace Frontier.CombinatoricsGraph

theorem sum_odds (n : ℕ) : ∑ i ∈ range n, (2*i+1) = n^2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring
