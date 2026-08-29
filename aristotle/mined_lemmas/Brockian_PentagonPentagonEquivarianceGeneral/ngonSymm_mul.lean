/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to be the first command, so the header above is a plain block
-- comment; the identical module docstring is repeated below.)
import Mathlib

/-!
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

open Complex DihedralGroup

/-!
## Setup

We generalize the `D₅` pentagon representation picture to an arbitrary regular `n`-gon.

* The vertices of the regular `n`-gon are labelled by `ZMod n`; the geometric realization of the
  vertex `k` is the complex number `ngonVertex n k = exp (2 π I k / n)`, obtained from Mathlib's
  additive character `ZMod.toCircle`.
* `ngonAct` is the combinatorial action of `DihedralGroup n` on the vertex labels `ZMod n`.
* `ngonSymm` is the geometric action of `DihedralGroup n` on `ℂ` by rotations `z ↦ ζₙ^i * z` and
  reflections `z ↦ ζₙ^(-i) * conj z`.

The main theorem `PentagonPentagonEquivarianceGeneral` says that the vertex realization map
intertwines these two actions, i.e. it is `DihedralGroup n`-equivariant.

The analytic content is supplied entirely by existing Mathlib results about the additive character
`ZMod.toCircle` (`Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean`), namely
`AddChar.map_add_eq_mul`, `AddChar.map_neg_eq_inv`, `Circle.coe_inv_eq_conj` and
`ZMod.injective_toCircle`.
-/

/-- The geometric realization of the vertex `k` of the regular `n`-gon:
`ngonVertex n k = exp (2 * π * I * k / n)`. -/

theorem ngonSymm_mul (n : ℕ) [NeZero n] (g h : DihedralGroup n) (z : ℂ) :
    ngonSymm n (g * h) z = ngonSymm n g (ngonSymm n h z) := by
  cases g with
  | r i =>
    cases h with
    | r j => simp [ngonSymm, ngonVertex_add, mul_assoc]
    | sr j =>
      simp only [DihedralGroup.r_mul_sr, ngonSymm]
      rw [show -(j - i) = i + -j by ring, ngonVertex_add, mul_assoc]
  | sr i =>
    cases h with
    | r j =>
      simp only [DihedralGroup.sr_mul_r, ngonSymm, map_mul, ← ngonVertex_neg]
      rw [show -(i + j) = -i + -j by ring, ngonVertex_add, mul_assoc]
    | sr j =>
      simp only [DihedralGroup.sr_mul_sr, ngonSymm, map_mul, ← ngonVertex_neg, neg_neg,
        Complex.conj_conj]
      rw [show j - i = -i + j by ring, ngonVertex_add, mul_assoc]

/-!
## Main theorem: equivariance of the vertex realization map
-/

/-- **Pentagon equivariance, generalized to arbitrary `n`-gons.**

The realization map sending the vertex label `k : ZMod n` of the regular `n`-gon to the complex
number `exp (2 π I k / n)` intertwines the combinatorial action `ngonAct` of the dihedral group
`DihedralGroup n` on the labels with the geometric action `ngonSymm` on `ℂ` by rotations and
reflections.  For `n = 5` this is the classical `D₅` pentagon representation statement. -/
