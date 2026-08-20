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

/-!
# Config Count Density Of BV
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_density_of_BV
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology
open scoped BigOperators Classical

namespace Brockian.EquidistributionBVReduction

/-- `configCount u S N` is the number of indices `n < N` whose sample `u n`
lands in the "configuration set" `S`. -/

lemma configCount_biUnion {ι : Type*} (u : ℕ → ℝ) (s : Finset ι) (S : ι → Set ℝ)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (S i) (S j)) (N : ℕ) :
    configCount u (⋃ i ∈ s, S i) N = ∑ i ∈ s, configCount u (S i) N := by
  classical
  have hset : ((Finset.range N).filter fun n => u n ∈ ⋃ i ∈ s, S i)
      = s.biUnion fun i => (Finset.range N).filter fun n => u n ∈ S i := by
    ext n
    simp [Set.mem_iUnion, and_left_comm]
  unfold configCount
  rw [hset]
  refine Finset.card_biUnion ?_
  intro i hi j hj hij
  refine Finset.disjoint_left.mpr ?_
  intro n hn hn'
  simp only [Finset.mem_filter] at hn hn'
  exact (hdisj i (by simpa using hi) j (by simpa using hj) hij).le_bot ⟨hn.2, hn'.2⟩

/-- **Configuration-count density from a bounded-variation (step) configuration set.**

If `u` is equidistributed in the unit interval and the configuration set is a finite union of
pairwise disjoint subintervals `[a i, b i) ⊆ [0, 1]` (equivalently: its indicator is a
`{0,1}`-valued function of bounded variation on `[0,1]`), then the proportion of indices
`n < N` realizing the configuration converges to the total length `∑ i, (b i - a i)`. -/
