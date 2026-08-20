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

noncomputable def ngonVertex (n : ℕ) (k : ZMod n) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ))

/-- The natural action of the dihedral group `DihedralGroup n` on the vertex indices
`ZMod n` of a regular `n`-gon: the rotation `r i` shifts indices, the reflection `sr i`
reverses them. -/
