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

theorem ConstellationLocalCountK3_pos (p : ℕ) [NeZero p] (hp : 3 < p) (h1 h2 h3 : ℤ)
    (h12 : (h1 : ZMod p) ≠ (h2 : ZMod p)) (h13 : (h1 : ZMod p) ≠ (h3 : ZMod p))
    (h23 : (h2 : ZMod p) ≠ (h3 : ZMod p)) :
    0 < localCount p {h1, h2, h3} := by
  rw [ConstellationLocalCountK3 p h1 h2 h3 h12 h13 h23]
  omega

end Brockian

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

