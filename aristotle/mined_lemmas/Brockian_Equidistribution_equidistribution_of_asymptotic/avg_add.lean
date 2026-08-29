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
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real Classical
open Filter MeasureTheory AddCircle

namespace Brockian.Equidistribution

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The Cesàro average of `f` along the first `N` terms of the sequence `u`. -/

lemma avg_add (u : ℕ → AddCircle T) (f g : C(AddCircle T, ℂ)) (N : ℕ) :
    avg u (f + g) N = avg u f N + avg u g N := by
  simp [avg, Finset.sum_add_distrib, mul_add]

omit hT in
