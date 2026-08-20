import Mathlib
open Finset
namespace MS.Combinatorics

/-- `MonoColor f c A` says that the finite set `A` is monochromatic of colour `c`
for the edge-colouring `f`. -/

theorem sum_first_n_odds (n : ℕ) : ∑ i ∈ range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; ring

