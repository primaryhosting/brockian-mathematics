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
# Equidistribution from transitive symmetry

If a symmetry group `G` acts transitively on a finite set `X`, then any normalized
`G`-invariant weight on `X` is the uniform distribution: every point carries weight
`1 / |X|`, and every subset `S` carries total weight `|S| / |X|`.

The same statement is given for probability measures: a `G`-invariant probability
measure on a finite `G`-set with transitive action is the uniform measure.

All statements here are unconditional: no auxiliary hypothesis is assumed beyond
transitivity, invariance and normalization.
-/

namespace Brockian
namespace EquidistributionUniformity

open Finset MeasureTheory
open scoped ENNReal

section Weights

variable {G X : Type*} [Group G] [MulAction G X]

/-- An invariant weight is constant along orbits; with a transitive action it is constant. -/

theorem measure_singleton_of_transitive_symmetry [MulAction.IsPretransitive G X]
    (mu : Measure X) [IsProbabilityMeasure mu] [SMulInvariantMeasure G X mu] (x : X) :
    mu {x} = (Fintype.card X : ℝ≥0∞)⁻¹ := by
  have hcard : (Fintype.card X : ℝ≥0∞) ≠ 0 := by
    have : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨x⟩
    exact_mod_cast this.ne'
  have hsum : ∑ y : X, mu {y} = 1 := by
    rw [MeasureTheory.sum_measure_singleton]
    simp
  have : (Fintype.card X : ℝ≥0∞) * mu {x} = 1 := by
    rw [← hsum, Finset.sum_congr rfl
      (fun y (_ : y ∈ (Finset.univ : Finset X)) => measure_singleton_eq_of_transitive
        (G := G) mu y x)]
    simp [Finset.card_univ]
  have hne : (Fintype.card X : ℝ≥0∞) ≠ ⊤ := by simp
  calc mu {x} = (Fintype.card X : ℝ≥0∞)⁻¹ * ((Fintype.card X : ℝ≥0∞) * mu {x}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hcard hne, one_mul]
    _ = (Fintype.card X : ℝ≥0∞)⁻¹ := by rw [this, mul_one]

end Measures

end EquidistributionUniformity
end Brockian


