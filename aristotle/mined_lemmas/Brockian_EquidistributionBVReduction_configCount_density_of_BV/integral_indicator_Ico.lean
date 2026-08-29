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
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators ENNReal
open Set Filter MeasureTheory

namespace Brockian
namespace EquidistributionBVReduction

/-! ## Variation of a difference -/

/-- The variation of a difference of two real-valued functions is at most the sum of the
variations. -/

theorem integral_indicator_Ico {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ t in (0 : ℝ)..1, Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ)) t) = b - a := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    MeasureTheory.setIntegral_indicator measurableSet_Ico]
  have hsub1 : Set.Ioo a b ⊆ Set.Ioc (0 : ℝ) 1 ∩ Set.Ico a b := fun t ht =>
    ⟨⟨lt_of_le_of_lt ha ht.1, le_of_lt (lt_of_lt_of_le ht.2 hb)⟩, ⟨le_of_lt ht.1, ht.2⟩⟩
  have hsub2 : Set.Ioc (0 : ℝ) 1 ∩ Set.Ico a b ⊆ Set.Ico a b := Set.inter_subset_right
  have hm : volume (Set.Ioc (0 : ℝ) 1 ∩ Set.Ico a b) = ENNReal.ofReal (b - a) := by
    refine le_antisymm ?_ ?_
    · simpa using measure_mono (μ := (volume : Measure ℝ)) hsub2
    · simpa using measure_mono (μ := (volume : Measure ℝ)) hsub1
  rw [MeasureTheory.setIntegral_const, measureReal_def, hm,
    ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ b - a), smul_eq_mul, mul_one]

/-! ## Configuration counts -/

open scoped Classical in
/-- `configCount x s N` is the number of indices `n < N` for which the fractional part of
`x n` lies in the "configuration set" `s`. -/
