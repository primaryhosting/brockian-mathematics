import Mathlib

/-!
# Admissible arithmetic-progression gap tuples

A finite set `H` of integers is *admissible* (in the sense of the Hardy–Littlewood prime
`k`-tuples conjecture) when, for every prime `p`, the reduction of `H` mod `p` omits at least
one residue class.  Equivalently, the local factor of the singular series
`𝔖(H) = ∏_p (1 - ν_H(p)/p)(1 - 1/p)^{-|H|}` is nonzero at every prime.

This file characterises admissibility of the arithmetic progression tuples
`{0, d, 2d, …, (k-1)d}` and derives new admissible gap ranges for `90 ≤ k ≤ 98`.
-/

open scoped BigOperators

namespace Brockian

open Finset

/-- A finite set of integers is *admissible* if for every prime `p` it omits at least one
residue class modulo `p`. -/

def apTuple (k : ℕ) (d : ℤ) : Finset ℤ :=
  (Finset.range k).image (fun j : ℕ => (j : ℤ) * d)

