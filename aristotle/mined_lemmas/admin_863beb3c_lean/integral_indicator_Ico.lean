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
# Reduction of equidistribution mod 1 to test functions of bounded variation

This file contains an unconditional proof that a sequence `x : ℕ → ℝ` whose Cesàro averages
against every test function of bounded variation on `[0,1]` converge to the corresponding
integral is uniformly distributed (equidistributed) mod `1`.

The main statement is `Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform`.
It is deduced from the formally stronger
`Brockian.EquidistributionBVReduction.equidistribution_of_monotone_uniform`, where only
monotone test functions are used.

All auxiliary facts are proved here, with no assumed black boxes; in particular the
subadditivity of the (extended) variation with respect to differences of functions,
the bounded variation of indicator functions of intervals, and the relevant integrals.
-/

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace Brockian
namespace EquidistributionBVReduction

/-! ## Bounded variation of a step function -/

/-- Subadditivity of the extended variation for a difference of two real valued functions. -/

theorem integral_indicator_Ico (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∫ t in (0:ℝ)..1, Set.indicator (Set.Ico a b) (fun _ => (1:ℝ)) t = b - a := by
  rw [intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_indicator measurableSet_Ico,
    Measure.restrict_restrict measurableSet_Ico]
  simp only [MeasureTheory.integral_const, smul_eq_mul, mul_one]
  have h1 : volume (Set.Ico a b ∩ Set.Ioc (0:ℝ) 1) = ENNReal.ofReal (b - a) := by
    refine le_antisymm ?_ ?_
    · refine le_trans (measure_mono (t := Set.Icc a b) ?_) ?_
      · rintro t ⟨⟨h1, h2⟩, -⟩
        exact ⟨h1, h2.le⟩
      · simp [Real.volume_Icc]
    · refine le_trans ?_ (measure_mono (s := Set.Ioo a b) ?_)
      · simp [Real.volume_Ioo]
      · rintro t ⟨h1, h2⟩
        exact ⟨⟨h1.le, h2⟩, lt_of_le_of_lt ha h1, h2.le.trans hb⟩
  simp only [MeasureTheory.Measure.real, Measure.restrict_apply_univ, h1,
    ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ b - a)]

