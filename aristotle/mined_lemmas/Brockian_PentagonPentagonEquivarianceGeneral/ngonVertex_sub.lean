/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian

/-- The `k`-th vertex of the regular `n`-gon inscribed in the unit circle of `ℂ`,
indexed by `k : ZMod n`. -/

lemma ngonVertex_sub (hn : 0 < n) (a b : ZMod n) :
    ngonVertex n (a - b) = ngonVertex n a * (starRingEnd ℂ) (ngonVertex n b) := by
  rw [sub_eq_add_neg, ngonVertex_add hn, ngonVertex_neg hn]

end Lemmas

/-- **Pentagon pentagon equivariance, general `n`-gon version.**

For every `n > 0`, the dihedral group `DihedralGroup n` acts both on the vertex index set
`ZMod n` of a regular `n`-gon and on the plane `ℂ` (rotations by `n`-th roots of unity,
reflections by conjugation composed with a rotation), and the vertex map
`k ↦ ngonVertex n k` intertwines the two actions.  The vertices all lie on the unit circle.

Specialising to `n = 5` recovers the `D₅` pentagon representation statement. -/
