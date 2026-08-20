import Mathlib
open Finset
namespace C2.Comb3

/-- Gauss' summation formula: `∑_{i<n} i = n(n-1)/2` (natural division is exact here). -/

theorem choose_symm (n k : ℕ) (h : k ≤ n) : n.choose k = n.choose (n-k) :=
  (Nat.choose_symm h).symm

end C2.Comb3

