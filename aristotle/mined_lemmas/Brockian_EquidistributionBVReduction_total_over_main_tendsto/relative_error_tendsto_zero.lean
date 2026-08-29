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
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology

namespace Brockian.EquidistributionBVReduction

/-- The *main term* of a Koksma-type (bounded-variation) equidistribution estimate:
for a sequence of length `N` and a mean value `I` (typically `I = ∫ x in (0:ℝ)..1, f x`),
the main term is `N * I`. -/

theorem relative_error_tendsto_zero
    (total disc : ℕ → ℝ) (I V : ℝ) (hI : I ≠ 0)
    (hdisc : Tendsto disc atTop (𝓝 0))
    (hKoksma : ∀ N, |total N - mainTerm I N| ≤ V * (N : ℝ) * disc N) :
    Tendsto (fun N => (total N - mainTerm I N) / mainTerm I N) atTop (𝓝 0) := by
  have hIabs : (0:ℝ) < |I| := abs_pos.mpr hI
  -- the comparison sequence `V * disc N / |I|` tends to `0`
  have hg : Tendsto (fun N : ℕ => V * disc N / |I|) atTop (𝓝 0) := by
    have : Tendsto (fun N : ℕ => V * disc N / |I|) atTop (𝓝 (V * 0 / |I|)) :=
      ((tendsto_const_nhds.mul hdisc).div_const _)
    simpa using this
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have habs : |mainTerm I N| = (N : ℝ) * |I| := by
    simp [mainTerm, abs_mul, abs_of_pos hNpos]
  rw [Real.norm_eq_abs, abs_div, habs, div_le_div_iff₀ (by positivity) hIabs]
  calc |total N - mainTerm I N| * |I|
      ≤ (V * (N : ℝ) * disc N) * |I| :=
        mul_le_mul_of_nonneg_right (hKoksma N) (le_of_lt hIabs)
    _ = V * disc N * ((N : ℝ) * |I|) := by ring

/-- **Total over main tends to one.**

Under a Koksma-type bounded-variation estimate `|total N - N * I| ≤ V * N * disc N`
with vanishing discrepancy `disc N → 0` and nonzero mean value `I ≠ 0`, the ratio of the
total sum to the main term tends to `1`. -/
