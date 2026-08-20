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

lemma lower_sum_le {g : ℝ → ℝ} (hg : MonotoneOn g (Icc (0 : ℝ) 1)) (x : ℕ → ℝ) (hk : 0 < k)
    (N : ℕ) :
    ∑ i ∈ Finset.range k,
        (configCount x (Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) * g ((i : ℝ) / k)
      ≤ ∑ n ∈ Finset.range N, g (Int.fract (x n)) := by
  rw [← sum_fiberwise x hk N (fun n => g (Int.fract (x n)))]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := (Finset.mem_range.1 hi).le
  rw [configCount_eq_card_fiber x hk i N, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun n hn => ?_
  have hidx : idx x k n = i := (Finset.mem_filter.1 hn).2
  have hmem := (idx_eq_iff x hk i n).1 hidx
  exact hg (div_mem_Icc hk hik) (fract_mem_Icc x n) hmem.1

/-- Upper Riemann sum bound for a monotone integrand. -/
