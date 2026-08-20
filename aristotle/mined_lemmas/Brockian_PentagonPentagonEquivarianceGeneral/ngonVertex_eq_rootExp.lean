import Mathlib

/-!
# Equivariance of the regular `n`-gon representation of the dihedral group

This file generalises the pentagon (`n = 5`, dihedral group `D₅`) picture to an arbitrary
regular `n`-gon.

The combinatorial model of the vertices of the `n`-gon is `ZMod n`, on which the dihedral group
`DihedralGroup n` acts by `r i • k = k + i` (rotation) and `sr i • k = -i - k` (reflection).

The geometric model is the set of `n`-th roots of unity in `ℂ`, on which `DihedralGroup n` acts by
`r i • z = ζ^i * z` and `sr i • z = ζ^(-i) * conj z`, where `ζ = exp (2πI / n)`.

The main result, `Brockian.PentagonPentagonEquivarianceGeneral`, says that the vertex map
`k ↦ exp (2πI k / n)` intertwines the two actions, for every `n > 0`.  The pentagon case is
recorded as `Brockian.pentagon_equivariance`.
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

open Complex

/-- The character `E n m = exp (2 π i m / n)`. -/

lemma ngonVertex_eq_rootExp (n : ℕ) (hn : 0 < n) (a : ℤ) :
    ngonVertex n ((a : ZMod n)) = rootExp n a := by
  refine rootExp_congr n hn ?_
  haveI : NeZero n := ⟨hn.ne'⟩
  push_cast
  simp [ZMod.natCast_val]

/-- The combinatorial action of the dihedral group on the vertex labels `ZMod n`. -/
