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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.EquidistributionBVReduction

open Filter Set MeasureTheory

/-- `configCount x S N` is the number of indices `n < N` whose fractional part
`Int.fract (x n)` lands in the "configuration window" `S`. -/

lemma tendsto_upperSum (hx : EquidistributedMod1 x) (G : ℝ → ℝ) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun N : ℕ =>
      (∑ i ∈ Finset.range k,
        G (((i : ℝ) + 1) / k) *
          (configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ)) / N)
      atTop (nhds (upperSum G k)) := by
  have hfun : ∀ N : ℕ,
      (∑ i ∈ Finset.range k,
        G (((i : ℝ) + 1) / k) *
          (configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ)) / N =
      ∑ i ∈ Finset.range k,
        G (((i : ℝ) + 1) / k) *
          ((configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) / N) := by
    intro N
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hfun]
  have hlim : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range k,
      G (((i : ℝ) + 1) / k) *
        ((configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ) / N))
      atTop (nhds (∑ i ∈ Finset.range k, G (((i : ℝ) + 1) / k) * (1 / k))) := by
    refine tendsto_finset_sum _ fun i hi => ?_
    exact tendsto_const_nhds.mul
      (tendsto_configCount_div x hx k i hk (Finset.mem_range.mp hi))
  have : (∑ i ∈ Finset.range k, G (((i : ℝ) + 1) / k) * (1 / k)) = upperSum G k := by
    simp only [upperSum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rwa [this] at hlim

