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

open Filter Topology Set MeasureTheory
open scoped BigOperators Classical

namespace Brockian.EquidistributionBVReduction

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` lies in `S`:
the count of "configurations" of the first `N` terms of the sequence inside the window `S`. -/

lemma tendsto_weighted_density {x : ℕ → ℝ} (hx : EquidistributedMod1 x) {k : ℕ} (hk : 0 < k)
    (w : ℕ → ℝ) :
    Tendsto (fun N : ℕ =>
        (∑ i ∈ Finset.range k,
          (configCount x (Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) * w i) / N)
      atTop (𝓝 (∑ i ∈ Finset.range k, w i / k)) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  simp only [Finset.sum_div]
  refine tendsto_finset_sum _ fun i hi => ?_
  have hik := Finset.mem_range.1 hi
  have h1 : (0 : ℝ) ≤ (i : ℝ) / k := by positivity
  have h3 : ((i : ℝ) + 1) / k ≤ 1 := by
    rw [div_le_one hk']
    have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hik
    linarith
  have hlim := hx ((i : ℝ) / k) (((i : ℝ) + 1) / k) h1 (node_le hk i) h3
  have hw : ((i : ℝ) + 1) / k - (i : ℝ) / k = 1 / k := by field_simp; ring
  rw [hw] at hlim
  have hmul := hlim.mul_const (w i)
  have heq : (fun N : ℕ =>
      ((configCount x (Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) / N) * w i)
      = fun N : ℕ =>
      ((configCount x (Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) * w i) / N := by
    funext N; ring
  rw [heq] at hmul
  have hval : 1 / (k : ℝ) * w i = w i / k := by ring
  rwa [hval] at hmul

/-- Birkhoff averages along an equidistributed sequence converge to the integral,
for a monotone integrand. -/
