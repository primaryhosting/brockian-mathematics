import Mathlib
open Finset
namespace C4.Comb5


theorem pascal (n k : ℕ) : (n+1).choose (k+1) = n.choose k + n.choose (k+1) :=
  Nat.choose_succ_succ n k

