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
# Reduction of equidistribution to bounded–variation test functions

Let `x : ℕ → ℝ` be a sequence.  We say that the *bounded variation averages of `x`
converge* if for every real function `f` of bounded variation on `[0,1]` the Birkhoff-type
averages of `f` along the fractional parts of `x` converge to `∫_0^1 f`.

The main result, `Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform`,
says that this hypothesis on `x` forces `x` to be uniformly distributed mod `1`:
the proportion of the first `N` fractional parts falling into a subinterval `[a,b) ⊆ [0,1]`
tends to its length `b - a`.

The point of the reduction is that indicator functions of intervals are of bounded
variation; this is proved here from scratch (`Brockian.EquidistributionBVReduction.boundedVariationOn_indicator_Ico`),
via a subadditivity estimate for `eVariationOn` and the fact that the two half-line
indicators `1_{[a,∞)}` and `1_{[b,∞)}` are monotone.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- A sequence `x : ℕ → ℝ` is *uniformly distributed mod 1* if for every subinterval
`[a,b) ⊆ [0,1]`, the proportion of `n < N` with `Int.fract (x n) ∈ [a, b)` tends to `b - a`. -/

theorem integral_indicator_Ico {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ t in (0 : ℝ)..1, Set.indicator (Set.Ico a b) (fun _ => (1 : ℝ)) t) = b - a := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [MeasureTheory.integral_indicator measurableSet_Ico]
  have hvol : (volume.restrict (Set.Ioc (0 : ℝ) 1)) (Set.Ico a b) = ENNReal.ofReal (b - a) := by
    rw [Measure.restrict_apply measurableSet_Ico]
    have h1 : Set.Ioo a b ⊆ Set.Ico a b ∩ Set.Ioc (0 : ℝ) 1 := by
      rintro t ⟨h1, h2⟩
      exact ⟨⟨h1.le, h2⟩, lt_of_le_of_lt ha h1, (h2.le.trans hb)⟩
    have h2 : Set.Ico a b ∩ Set.Ioc (0 : ℝ) 1 ⊆ Set.Icc a b := fun t ht => ⟨ht.1.1, ht.1.2.le⟩
    have hle1 := measure_mono (μ := (volume : Measure ℝ)) h1
    have hle2 := measure_mono (μ := (volume : Measure ℝ)) h2
    rw [Real.volume_Ioo] at hle1
    rw [Real.volume_Icc] at hle2
    exact le_antisymm hle2 hle1
  simp only [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one]
  rw [MeasureTheory.measureReal_def, hvol, ENNReal.toReal_ofReal (by linarith)]

/-! ### The main reduction -/

/-- **Reduction of equidistribution to bounded variation test functions.**
If the averages along `x` of every function of bounded variation on `[0,1]` converge to the
corresponding integral, then `x` is uniformly distributed mod `1`. -/
