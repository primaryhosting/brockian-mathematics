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
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory Filter Topology Set

namespace Brockian.EquidistributionBVReduction

open scoped Classical in
/-- `configCount x A N` is the number of indices `n < N` whose orbit point `x n`,
reduced mod `1`, lands in the configuration set `A`. -/

lemma sum_fiber_lower (x : ℕ → ℝ) (hg : MonotoneOn g (Set.Icc (0:ℝ) 1)) {K : ℕ} (hK : 0 < K)
    (N : ℕ) :
    ∑ j ∈ Finset.range K,
        (configCount x (Set.Ico ((j : ℝ) / K) (((j : ℝ) + 1) / K)) N : ℝ) * g ((j : ℝ) / K)
      ≤ ∑ n ∈ Finset.range N, g (Int.fract (x n)) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (floor_mem_range x hK N) (fun n => g (Int.fract (x n)))]
  refine Finset.sum_le_sum ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [configCount_eq_card_fiber x hK j N]
  have hmem := div_mem_Icc_of_le hK hj.le
  have key := Finset.card_nsmul_le_sum
    ((Finset.range N).filter (fun n => ⌊(K:ℝ) * Int.fract (x n)⌋₊ = j))
    (fun n => g (Int.fract (x n))) (g ((j:ℝ)/K)) ?_
  · simpa [nsmul_eq_mul] using key
  · intro n hn
    simp only [Finset.mem_filter] at hn
    have h2 := (floor_mul_eq_iff_mem_Ico hK j (Int.fract_nonneg (x n))).1 hn.2
    exact hg hmem ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩ h2.1

/-- Upper Riemann-type bound for the orbit sum of a monotone function. -/
