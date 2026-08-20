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
# Sing Uniform Of Transitive
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.sing_uniform_of_transitive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open MeasureTheory ENNReal

namespace Brockian.EquidistributionUniformity

/-- **Uniformity from transitivity.**

If a group `G` acts on a finite measurable space `X` (with measurable singletons), and `μ` is
a probability measure on `X` whose singleton masses are invariant under the action, then
transitivity of the action forces `μ` to be the uniform measure: every singleton has mass
`1 / |X|`.

The transitivity assumption is stated in elementary form (`∀ x y, ∃ g, g • x = y`) and is
genuinely used inside the proof: it shows all singleton masses agree, after which the total
mass `1` is split equally among the `|X|` points. -/
theorem sing_uniform_of_transitive {G X : Type*} [Group G] [MulAction G X]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hinv : ∀ (g : G) (x : X), μ {g • x} = μ {x})
    (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x : X) :
    μ {x} = 1 / (Fintype.card X : ℝ≥0∞) := by
  have hconst : ∀ y : X, μ {y} = μ {x} := by
    intro y
    obtain ⟨g, rfl⟩ := htrans x y
    exact hinv g x
  have hsum : ∑ y : X, μ {y} = 1 := by
    rw [MeasureTheory.sum_measure_singleton]
    simp
  rw [Finset.sum_congr rfl (fun y _ => hconst y)] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hcard : (Fintype.card X : ℝ≥0∞) ≠ 0 := by
    have hne : Fintype.card X ≠ 0 := by
      intro h
      rw [Fintype.card_eq_zero_iff] at h
      exact h.elim' x
    simpa using hne
  rw [ENNReal.eq_div_iff hcard (by simp)]
  exact hsum

/-- Real-valued form of the previous theorem: the mass of each point, as a real number, is
`1 / |X|`. -/
theorem sing_uniform_real_of_transitive {G X : Type*} [Group G] [MulAction G X]
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hinv : ∀ (g : G) (x : X), μ {g • x} = μ {x})
    (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x : X) :
    (μ {x}).toReal = 1 / (Fintype.card X : ℝ) := by
  rw [sing_uniform_of_transitive μ hinv htrans x]
  simp

end Brockian.EquidistributionUniformity

