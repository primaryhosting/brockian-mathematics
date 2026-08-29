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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Filter Set MeasureTheory Topology

namespace Brockian.EquidistributionBVReduction

/-- The indicator function of the half-open interval `[a, b)`, as a real-valued function. -/

lemma indicatorIco_boundedVariationOn {a b : ℝ} (hab : a ≤ b) :
    BoundedVariationOn (indicatorIco a b) (Set.Icc (0 : ℝ) 1) := by
  rw [BoundedVariationOn, indicatorIco_eq_sub hab]
  refine ne_top_of_le_ne_top ?_ (eVariationOn_sub_le _ _)
  exact ENNReal.add_ne_top.2
    ⟨boundedVariationOn_of_monotone (indicatorIci_monotone a),
      boundedVariationOn_of_monotone (indicatorIci_monotone b)⟩

