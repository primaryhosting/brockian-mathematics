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

lemma cesaroAvg_smul (c : ℂ) (g : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    cesaroAvg x (⇑(c • g)) N = c * cesaroAvg x g N := by
  simp only [cesaroAvg, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

