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

theorem ngonSymm_one (n : ℕ) [NeZero n] (z : ℂ) : ngonSymm n (1 : DihedralGroup n) z = z := by
  show ngonSymm n (DihedralGroup.r 0) z = z
  simp [ngonSymm]

