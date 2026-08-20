import Mathlib

open scoped BigOperators
open scoped Classical

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Local constellation counts

For a *constellation* (admissible tuple) `H = (h₁, …, h_k)` of integer shifts, the
*local count* at a modulus `p` is the number of residue classes `a mod p` for which none of
`a + h₁, …, a + h_k` is divisible by `p`; equivalently, the number of `a : ZMod p` with
`a + hᵢ ≠ 0` for all `i`.

This file gives the general closed formula (`Brockian.localCount_eq`) and specializes it to
tuples of length one, two and three; the `k = 3` case is
`Brockian.ConstellationLocalCountK3`, with an arithmetic (divisibility) restatement in
`Brockian.ConstellationLocalCountK3_dvd`.
-/

namespace Brockian

/-- The local constellation count of the shift set `H` at modulus `p`: the number of residues
`a : ZMod p` such that `a + h ≠ 0` for every shift `h ∈ H`. -/

theorem ConstellationLocalCountK0 (p : ℕ) [NeZero p] : localCount p (∅ : Finset ℤ) = p := by
  simp [localCount_eq]

/-- A one-element constellation forbids exactly one residue class. -/
