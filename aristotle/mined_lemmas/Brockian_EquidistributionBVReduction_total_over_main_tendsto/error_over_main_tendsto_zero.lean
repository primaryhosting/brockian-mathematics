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
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Filter Topology

namespace Brockian.EquidistributionBVReduction

/-- The *main term* of the equidistribution / bounded-variation reduction: the
expected value `N * I` of the first `N` sampled values, where `I` is the mean
(integral) of the sampled function. -/

lemma error_over_main_tendsto_zero (f : ℕ → ℝ) (I C : ℝ) (hI : I ≠ 0)
    (hbv : ∀ N, |total f N - main I N| ≤ C) :
    Tendsto (fun N : ℕ => (total f N - main I N) / main I N) atTop (𝓝 0) := by
  have hbound : ∀ᶠ N : ℕ in atTop,
      ‖(total f N - main I N) / main I N‖ ≤ (C / |I|) / (N : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hIpos : (0 : ℝ) < |I| := abs_pos.mpr hI
    have hrw : ‖(total f N - main I N) / main I N‖
        = |total f N - main I N| / ((N : ℝ) * |I|) := by
      rw [Real.norm_eq_abs, abs_div]
      simp [main, abs_mul, abs_of_pos hNpos]
    rw [hrw, div_le_div_iff₀ (by positivity) hNpos]
    calc |total f N - main I N| * (N : ℝ)
        ≤ C * (N : ℝ) := mul_le_mul_of_nonneg_right (hbv N) hNpos.le
      _ = C / |I| * ((N : ℝ) * |I|) := by field_simp
  exact squeeze_zero_norm' hbound (tendsto_const_div_atTop_nhds_zero_nat _)

/-- **Total over main tends to one.**

In the bounded-variation reduction for equidistribution sums, the total sum
`total f N = ∑_{n < N} f n` differs from the main term `main I N = N * I` by a
uniformly bounded error (a Koksma–Hlawka type bound, with `C` controlled by the
total variation of the sampled function). Provided the mean `I` is nonzero, the
ratio `total / main` tends to `1`. -/
