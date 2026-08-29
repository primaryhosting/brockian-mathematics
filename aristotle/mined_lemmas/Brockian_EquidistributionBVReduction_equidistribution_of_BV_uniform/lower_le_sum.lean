import Mathlib
import RequestProject.Brockian.EquidistributionBVReduction

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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset Set
open scoped Topology BigOperators Classical

set_option maxHeartbeats 1000000

namespace Brockian
namespace EquidistributionBVReduction

/-- `countIn x a b N` is the number of indices `n < N` with `x n ∈ [a, b)`. -/

lemma lower_le_sum (hx : ∀ n, x n ∈ Set.Ico (0 : ℝ) 1) (hg : MonotoneOn g (Set.Icc 0 1))
    (hk : 0 < k) (N : ℕ) :
    ∑ j ∈ Finset.range k,
        g ((j : ℝ) / k) * (countIn x ((j : ℝ) / k) (((j : ℝ) + 1) / k) N : ℝ) ≤
      ∑ n ∈ Finset.range N, g (x n) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Finset.sum_fiberwise_of_maps_to (floor_mem_range hx hk N) (fun n => g (x n))]
  refine Finset.sum_le_sum ?_
  intro j hj
  have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast Finset.mem_range.1 hj
  have hmem0 : (j : ℝ) / k ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, by rw [div_le_one hk']; linarith⟩
  rw [fiber_eq_filter_Ico (fun n => (hx n).1) hk j N]
  have hb : ∀ n ∈ ((Finset.range N).filter
      (fun n => x n ∈ Set.Ico ((j : ℝ) / k) (((j : ℝ) + 1) / k))),
      g ((j : ℝ) / k) ≤ g (x n) := by
    intro n hn
    exact hg hmem0 ⟨(hx n).1, (hx n).2.le⟩ (Finset.mem_filter.1 hn).2.1
  calc g ((j : ℝ) / k) * (countIn x ((j : ℝ) / k) (((j : ℝ) + 1) / k) N : ℝ)
      = _ • g ((j : ℝ) / k) := by rw [nsmul_eq_mul, countIn]; ring
    _ ≤ ∑ n ∈ _, g (x n) := Finset.card_nsmul_le_sum _ _ _ hb

/-- The normalized weighted counting sums converge to the corresponding Darboux sums. -/
