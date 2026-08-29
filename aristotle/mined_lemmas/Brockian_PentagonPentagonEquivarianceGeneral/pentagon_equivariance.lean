/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean does not allow a module docstring `/-!  -/` to precede `import`, so the header
is repeated below as the module docstring, verbatim.)
-/

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

open DihedralGroup Complex

/-! ## Vertices of a regular `n`-gon

The `k`-th vertex of the standard regular `n`-gon inscribed in the unit circle of `ℂ` is
`exp (2 π i k / n)`.  This only depends on `k` modulo `n`, so it is naturally indexed by
`ZMod n`; Mathlib already packages this as the additive character `ZMod.toCircle`.
-/

/-- The `k`-th vertex of the standard regular `n`-gon, as a complex number.
It equals `exp (2 * π * I * k / n)` (see `Brockian.ngonVertex_eq_exp`). -/

theorem pentagon_equivariance (g : DihedralGroup 5) (k : ZMod 5) :
    dihedralPlane 5 g (ngonVertex 5 k) = ngonVertex 5 (dihedralIdx 5 g k) :=
  (PentagonPentagonEquivarianceGeneral 5).2.2.2.2 g k

/-- The vertices of the regular `n`-gon are exactly the `n`-th roots of unity. -/
