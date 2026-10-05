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
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Finset MeasureTheory
open scoped Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- A sequence `x : ℕ → ℝ` with values in `[0, 1)` is *uniformly distributed* if for every
`c ∈ [0, 1]` the proportion of the first `N` terms lying in `[0, c)` tends to `c`. -/

lemma count_interval_tendsto (hx : UniformlyDistributed x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (((range N).filter (fun n => a ≤ x n ∧ x n < b)).card : ℝ) / N)
      atTop (𝓝 (b - a)) := by
  obtain ⟨-, hlim⟩ := hx
  have hcard : ∀ N : ℕ,
      ((range N).filter (fun n => x n < a)).card
        + ((range N).filter (fun n => a ≤ x n ∧ x n < b)).card
      = ((range N).filter (fun n => x n < b)).card := by
    intro N
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext n
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro (⟨hn, h⟩ | ⟨hn, -, h⟩)
        · exact ⟨hn, lt_of_lt_of_le h hab⟩
        · exact ⟨hn, h⟩
      · rintro ⟨hn, h⟩
        rcases lt_or_ge (x n) a with h' | h'
        · exact Or.inl ⟨hn, h'⟩
        · exact Or.inr ⟨hn, h', h⟩
    · rw [Finset.disjoint_left]
      rintro n hn1 hn2
      simp only [Finset.mem_filter] at hn1 hn2
      linarith [hn1.2, hn2.2.1]
  have hA := hlim a ⟨ha, hab.trans hb⟩
  have hB := hlim b ⟨ha.trans hab, hb⟩
  refine (hB.sub hA).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have h := hcard N
  field_simp
  push_cast [← h]
  ring

end Counting

/-- Membership in the `i`-th fiber of the floor map. -/
