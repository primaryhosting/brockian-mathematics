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

/-
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Topology AddCircle

namespace Brockian.Equidistribution

/-- The Cesàro (Birkhoff) average of `f` along the first `N` terms of the sequence `x`. -/

lemma norm_integral_le (f : C(AddCircle (1 : ℝ), ℂ)) :
    ‖∫ t, f t ∂(haarAddCircle (T := 1))‖ ≤ ‖f‖ := by
  simpa using norm_integral_le_of_norm_le_const (μ := haarAddCircle (T := 1)) (C := ‖f‖)
    (f := fun t => f t) (Filter.Eventually.of_forall fun t => f.norm_coe_le_norm t)

/-- Under the Weyl hypothesis, the Cesàro averages of every element of the span of the
Fourier characters converge to the corresponding integral. -/
