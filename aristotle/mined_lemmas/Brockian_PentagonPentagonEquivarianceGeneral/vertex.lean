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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

open Complex DihedralGroup

/-! ## Vertices of the regular `n`-gon

The vertices of the regular `n`-gon inscribed in the unit circle of `ℂ` are indexed by
`ZMod n`; the vertex with index `k` is `exp (2 * π * I * k / n)`.  We use Mathlib's additive
character `ZMod.toCircle : AddChar (ZMod N) Circle`, so that the "rotation" identity
`vertex (a + b) = vertex a * vertex b` is inherited from `AddChar.map_add_eq_mul`. -/

/-- The `k`-th vertex of the regular `n`-gon inscribed in the unit circle of `ℂ`,
namely `exp (2 * π * I * k / n)`. -/

noncomputable def vertex (n : ℕ) [NeZero n] (k : ZMod n) : ℂ := (ZMod.toCircle k : ℂ)

variable {n : ℕ} [NeZero n]

