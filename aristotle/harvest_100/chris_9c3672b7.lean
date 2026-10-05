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
noncomputable def mainTerm (I : ℝ) (N : ℕ) : ℝ := (N : ℝ) * I

@[simp]
theorem mainTerm_apply (I : ℝ) (N : ℕ) : mainTerm I N = (N : ℝ) * I := rfl

/-- The relative error of a Koksma-type estimate tends to `0`.

If the total sum `total N` differs from the main term `N * I` by at most
`V * N * disc N` (the Koksma–Hlawka bound: total variation `V` times the number of terms
times the discrepancy `disc N`) and the discrepancy tends to `0` (equidistribution),
then `(total N - mainTerm I N) / mainTerm I N → 0`. -/
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
theorem total_over_main_tendsto
    (total disc : ℕ → ℝ) (I V : ℝ) (hI : I ≠ 0)
    (hdisc : Tendsto disc atTop (𝓝 0))
    (hKoksma : ∀ N, |total N - mainTerm I N| ≤ V * (N : ℝ) * disc N) :
    Tendsto (fun N => total N / mainTerm I N) atTop (𝓝 1) := by
  have h := relative_error_tendsto_zero total disc I V hI hdisc hKoksma
  have h1 : Tendsto (fun N => (total N - mainTerm I N) / mainTerm I N + 1) atTop (𝓝 (0 + 1)) :=
    h.add tendsto_const_nhds
  rw [zero_add] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hmain : mainTerm I N ≠ 0 := mul_ne_zero (ne_of_gt hNpos) hI
  field_simp
  ring

/-- Sanity check: the hypotheses of `total_over_main_tendsto` are satisfiable non-trivially.
Here `total N = N + 1` (for `N ≥ 1`), main term `N * 1`, variation `V = 1` and
discrepancy `disc N = 1 / N`. -/
example :
    Tendsto (fun N : ℕ => (if N = 0 then 0 else (N : ℝ) + 1) / mainTerm 1 N) atTop (𝓝 1) := by
  refine total_over_main_tendsto _ (fun N => ((N : ℝ))⁻¹) 1 1 one_ne_zero
    (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop) ?_
  intro N
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h, mainTerm]
  · have hN : (0:ℝ) < (N : ℝ) := by exact_mod_cast h
    rw [if_neg (by omega)]
    have : (N : ℝ) + 1 - mainTerm 1 N = 1 := by simp [mainTerm]
    rw [this, abs_one, one_mul, mul_inv_cancel₀ (ne_of_gt hN)]

end Brockian.EquidistributionBVReduction

