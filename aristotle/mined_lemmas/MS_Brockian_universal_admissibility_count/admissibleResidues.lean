import Mathlib
open Matrix Finset
namespace MS.Brockian
/-- Universal q−2 admissibility law (heart of the Brockian sieve). -/

def admissibleResidues (q : ℕ) [NeZero q] (g : ZMod q) : Finset (ZMod q) :=
  Finset.univ.filter (fun r => r ≠ 0 ∧ r ≠ -g)
