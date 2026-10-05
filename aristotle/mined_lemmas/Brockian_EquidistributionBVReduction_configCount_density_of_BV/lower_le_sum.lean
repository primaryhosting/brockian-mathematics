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

lemma lower_le_sum (G : ℝ → ℝ) (hG : Monotone G) (k N : ℕ) (hk : 0 < k) :
    (∑ i ∈ Finset.range k,
        G ((i : ℝ) / k) * (configCount x (Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)) N : ℝ)) ≤
      ∑ n ∈ Finset.range N, G (Int.fract (x n)) := by
  rw [sum_fiberwise x G k N hk]
  simp only [configCount_Ico_eq_card]
  refine Finset.sum_le_sum fun i _ => ?_
  have hb : ∀ n ∈ ((Finset.range N).filter fun n =>
      Int.fract (x n) ∈ Set.Ico ((i : ℝ) / k) (((i : ℝ) + 1) / k)),
      G ((i : ℝ) / k) ≤ G (Int.fract (x n)) := by
    intro n hn
    simp only [Finset.mem_filter, Set.mem_Ico] at hn
    exact hG hn.2.1
  have h2 := Finset.card_nsmul_le_sum _ _ _ hb
  rw [nsmul_eq_mul, mul_comm] at h2
  exact h2

