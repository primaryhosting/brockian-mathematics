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

lemma integral_indicatorIco {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ t in (0:ℝ)..1, indicatorIco a b t) = b - a := by
  have hvol : volume (Set.Ico a b ∩ Set.Ioc (0:ℝ) 1) = ENNReal.ofReal (b - a) := by
    refine le_antisymm ?_ ?_
    · calc volume (Set.Ico a b ∩ Set.Ioc (0:ℝ) 1) ≤ volume (Set.Icc a b) :=
            measure_mono fun t ht => ⟨ht.1.1, ht.1.2.le⟩
        _ = ENNReal.ofReal (b - a) := by rw [Real.volume_Icc]
    · calc ENNReal.ofReal (b - a) = volume (Set.Ioo a b) := by rw [Real.volume_Ioo]
        _ ≤ volume (Set.Ico a b ∩ Set.Ioc (0:ℝ) 1) :=
            measure_mono fun t ht => ⟨⟨ht.1.le, ht.2⟩, lt_of_le_of_lt ha ht.1, ht.2.le.trans hb⟩
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  unfold indicatorIco
  rw [MeasureTheory.integral_indicator measurableSet_Ico,
    MeasureTheory.Measure.restrict_restrict measurableSet_Ico,
    MeasureTheory.integral_const]
  simp [MeasureTheory.measureReal_def, hvol,
    ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ b - a)]

