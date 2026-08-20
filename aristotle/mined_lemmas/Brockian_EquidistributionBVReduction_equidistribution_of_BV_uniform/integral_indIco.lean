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
# Reduction of equidistribution to bounded-variation test functions

Let `x : ℕ → ℝ` be a sequence.  Assume that for **every** real function `f` of bounded
variation on `[0,1]` the Birkhoff-type averages

`(1/N) * ∑_{n < N} f (Int.fract (x n))`

converge to `∫₀¹ f`.  We show that the sequence `x` is then equidistributed modulo one, and
moreover *uniformly* so: the counting error over intervals `[a,b) ⊆ [0,1]` tends to `0`
uniformly in the endpoints (i.e. the discrepancy of the sequence tends to `0`).

The main statement is `equidistribution_of_BV_uniform`.  It is unconditional: apart from the
assumption on the sequence itself, no auxiliary result is taken as a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace Brockian

open scoped Classical in
/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

theorem integral_indIco {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ t in (0:ℝ)..1, indIco a b t) = b - a := by
  have hind : indIco a b = Set.indicator (Set.Ico a b) (fun _ => (1:ℝ)) := by
    funext t; simp [indIco, Set.indicator_apply]
  have hsub : Set.Ioo a b ⊆ Set.Ioc (0:ℝ) 1 ∩ Set.Ico a b := by
    intro t ht
    exact ⟨⟨lt_of_le_of_lt ha ht.1, ht.2.le.trans hb⟩, ⟨ht.1.le, ht.2⟩⟩
  have h1 : volume (Set.Ioc (0:ℝ) 1 ∩ Set.Ico a b) = ENNReal.ofReal (b - a) := by
    apply le_antisymm
    · calc volume (Set.Ioc (0:ℝ) 1 ∩ Set.Ico a b) ≤ volume (Set.Icc a b) :=
            measure_mono (fun t ht => ⟨ht.2.1, ht.2.2.le⟩)
        _ = ENNReal.ofReal (b - a) := by rw [Real.volume_Icc]
    · calc ENNReal.ofReal (b - a) = volume (Set.Ioo a b) := by rw [Real.volume_Ioo]
        _ ≤ _ := measure_mono hsub
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), hind,
    MeasureTheory.setIntegral_indicator measurableSet_Ico]
  simp only [MeasureTheory.integral_const, smul_eq_mul, mul_one,
    MeasureTheory.measureReal_def, MeasureTheory.Measure.restrict_apply_univ]
  rw [h1, ENNReal.toReal_ofReal (by linarith)]

/-- The Birkhoff sum of an interval indicator is the corresponding counting function. -/
