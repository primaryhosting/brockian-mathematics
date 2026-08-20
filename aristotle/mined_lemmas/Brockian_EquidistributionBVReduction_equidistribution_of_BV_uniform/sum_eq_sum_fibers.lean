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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Finset MeasureTheory
open scoped Topology BigOperators Classical

namespace Brockian
namespace EquidistributionBVReduction

/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

lemma sum_eq_sum_fibers (x : ℕ → ℝ) (g : ℝ → ℝ) {K : ℕ} (hK : 0 < K) (N : ℕ) :
    ∑ n ∈ Finset.range N, g (Int.fract (x n)) =
      ∑ i ∈ Finset.range K,
        ∑ n ∈ (Finset.range N).filter
          (fun n => Int.fract (x n) ∈ Set.Ico ((i : ℝ) / K) (((i : ℝ) + 1) / K)),
          g (Int.fract (x n)) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hmaps : ∀ n ∈ Finset.range N, ⌊(K : ℝ) * Int.fract (x n)⌋₊ ∈ Finset.range K := by
    intro n _
    refine Finset.mem_range.2 ?_
    have h1 : Int.fract (x n) < 1 := Int.fract_lt_one _
    have : (K : ℝ) * Int.fract (x n) < (K : ℝ) := by nlinarith
    exact Nat.floor_lt' (by omega) |>.2 (by simpa using this)
  have := Finset.sum_fiberwise_of_maps_to hmaps (fun n => g (Int.fract (x n)))
  rw [← this]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  refine Finset.filter_congr (fun n _ => ?_)
  simpa using floor_eq_iff_mem_Ico hK (Int.fract_nonneg (x n)) i

/-- Lower step-function bound for the partial sums. -/
