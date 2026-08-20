/-
# Carleson
Category: Frontier Math
Target: Math2.carleson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not allow a module docstring before the import line, so the
required header is reproduced here as a plain comment and again as a module
docstring immediately after the import.)
-/

import Mathlib

/-!
# Carleson
Category: Frontier Math
Target: Math2.carleson
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

namespace Math2

open MeasureTheory Filter Topology
open scoped ENNReal

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The `N`-th symmetric partial sum of the Fourier series of `f` at the point `x`. -/

theorem tendstoInMeasure_fourierPartialSum (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    TendstoInMeasure (@AddCircle.haarAddCircle T hT)
      (fun N => fourierPartialSum (⇑f) N) atTop (⇑f) :=
  (tendstoInMeasure_of_tendsto_Lp (tendsto_fourierPartialSumLp f)).congr
    (fun N => coeFn_fourierPartialSumLp f N) (Filter.EventuallyEq.refl _ _)

/-- **Carleson-type theorem (subsequence form).**  For every `f` in `L²` of the circle
`AddCircle T`, there is a strictly increasing sequence of cut-offs `ns` along which the
symmetric partial sums of the Fourier series of `f` converge to `f` almost everywhere.

This is the almost-everywhere convergence statement for a subsequence of cut-offs
(depending on `f`); the full Carleson theorem, in which the almost-everywhere
convergence holds along *all* cut-offs `N → ∞`, is stated in the comment below and is
not proved here. -/
