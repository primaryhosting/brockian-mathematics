import Mathlib
open Finset
namespace C2.Comb3

/-- Gauss' summation formula: `∑_{i<n} i = n(n-1)/2` (natural division is exact here). -/

theorem sum_range_id (n : ℕ) : ∑ i ∈ range n, i = n*(n-1)/2 := Finset.sum_range_id n

/-- Nicomachus' theorem: the sum of the first `n+1` cubes is the square of their sum. -/
