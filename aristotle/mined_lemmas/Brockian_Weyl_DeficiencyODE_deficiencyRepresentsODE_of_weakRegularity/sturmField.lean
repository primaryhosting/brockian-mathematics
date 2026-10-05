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

import Mathlib

/-!
# Deficiency Represents ODE Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.deficiencyRepresentsODE_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

open Set MeasureTheory

namespace Brockian.Weyl.DeficiencyODE

/-- **Weak regularity** of a potential `q : ℝ → ℂ`: `q` is bounded on every compact interval.
This is much weaker than continuity of `q`; it is exactly what is needed to run the Gronwall
argument behind uniqueness for the Sturm–Liouville system. -/

private def sturmField (q : ℝ → ℂ) (z : ℂ) : ℝ → (ℂ × ℂ) → (ℂ × ℂ) :=
  fun t x => (x.2, (q t - z) * x.1)

