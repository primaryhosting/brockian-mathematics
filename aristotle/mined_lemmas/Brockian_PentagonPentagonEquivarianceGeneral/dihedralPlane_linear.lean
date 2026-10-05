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

theorem dihedralPlane_linear (n : ℕ) [NeZero n] (g : DihedralGroup n) (a b : ℝ) (z w : ℂ) :
    dihedralPlane n g ((a : ℂ) * z + (b : ℂ) * w) =
      (a : ℂ) * dihedralPlane n g z + (b : ℂ) * dihedralPlane n g w := by
  cases g with
  | r i => simp only [dihedralPlane]; ring
  | sr i =>
    simp only [dihedralPlane, map_add, map_mul, Complex.conj_ofReal]
    ring

/-! ## The general equivariance theorem -/

/--
**Pentagon equivariance, in general.**  For every `n ≥ 1` the labelling map
`k ↦ ngonVertex n k` sending a vertex label of the regular `n`-gon to the corresponding point
`exp (2 π i k / n)` of the plane intertwines the combinatorial action of the dihedral group
`D_n` on the labels `ZMod n` with its geometric action on `ℂ`.

The statement records that both are genuine (left) actions of `DihedralGroup n` — they send
`1` to the identity and products to composites — and that the vertex map is equivariant.
Taking `n = 5` recovers the pentagon (`D_5`) case, see
`Brockian.pentagon_equivariance`.
-/
