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

theorem ConstellationLocalCountK3_dvd (p : ℕ) [NeZero p] (h1 h2 h3 : ℤ)
    (h12 : ¬ ((p : ℤ) ∣ (h1 - h2))) (h13 : ¬ ((p : ℤ) ∣ (h1 - h3)))
    (h23 : ¬ ((p : ℤ) ∣ (h2 - h3))) :
    localCount p {h1, h2, h3} = p - 3 :=
  ConstellationLocalCountK3 p h1 h2 h3
    ((intCast_ne_intCast_iff_not_dvd p h1 h2).2 h12)
    ((intCast_ne_intCast_iff_not_dvd p h1 h3).2 h13)
    ((intCast_ne_intCast_iff_not_dvd p h2 h3).2 h23)

/-- For a prime `p > 3` a `3`-shift constellation with pairwise distinct shifts mod `p` still
admits a residue class, i.e. the local count is positive. -/
