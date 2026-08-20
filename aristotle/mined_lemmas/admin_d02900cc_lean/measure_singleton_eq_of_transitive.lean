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

If a group `G` acts transitively on a finite set `X` and `μ` is a `G`-invariant probability
measure on `X`, then `μ` is the uniform measure: every singleton has measure `1 / |X|`.

The main result is `Brockian.EquidistributionUniformity.sing_uniform_of_transitive`.
-/

open MeasureTheory
open scoped ENNReal

namespace Brockian.EquidistributionUniformity

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
variable {G : Type*} [Group G] [MulAction G X]

omit [MeasurableSingletonClass X] in
/-- Under a transitive action by measure-preserving transformations, all singletons have the
same measure. -/

theorem measure_singleton_eq_of_transitive (μ : Measure X) [SMulInvariantMeasure G X μ]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x y : X) : μ {x} = μ {y} := by
  obtain ⟨g, hg⟩ := htrans x y
  have hpre : (fun z => g • z) ⁻¹' ({y} : Set X) = {x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact MulAction.injective g (h.trans hg.symm)
    · rintro rfl
      exact hg
  calc μ {x} = μ ((fun z => g • z) ⁻¹' ({y} : Set X)) := by rw [hpre]
    _ = μ {y} := measure_preimage_smul μ g _

/-- The total mass of a probability measure on a finite space is the sum of the masses of the
singletons. -/
