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

theorem integral_step (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) : ∫ t in (0:ℝ)..1, step c t = 1 - c := by
  have hst : step c = Set.indicator (Set.Ici c) (fun _ => (1:ℝ)) := by
    funext t; simp [step, Set.indicator_apply, Set.mem_Ici]
  rw [hst, intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  simp only [MeasureTheory.integral_const, smul_eq_mul, mul_one]
  have h1 : volume (Set.Ici c ∩ Set.Ioc (0:ℝ) 1) = ENNReal.ofReal (1 - c) := by
    refine le_antisymm ?_ ?_
    · refine le_trans (measure_mono (t := Set.Icc c 1) ?_) ?_
      · rintro t ⟨h1, -, h2⟩
        exact ⟨h1, h2⟩
      · simp [Real.volume_Icc]
    · refine le_trans ?_ (measure_mono (s := Set.Ioo c 1) ?_)
      · simp [Real.volume_Ioo]
      · rintro t ⟨h1, h2⟩
        exact ⟨h1.le, lt_of_le_of_lt hc h1, h2.le⟩
  simp only [MeasureTheory.Measure.real, Measure.restrict_apply_univ, h1,
    ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - c)]

/-! ## Equidistribution -/

/-- A sequence `x : ℕ → ℝ` is *equidistributed mod 1* if, for every subinterval `[a,b) ⊆ [0,1]`,
the proportion of the first `N` fractional parts `Int.fract (x n)` lying in `[a, b)` converges
to the length `b - a`. -/
