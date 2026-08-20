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

theorem eq_inv_card_smul_count_of_transitive [Fintype X] (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G X μ] (htrans : ∀ x y : X, ∃ g : G, g • x = y) :
    μ = (Fintype.card X : ℝ≥0∞)⁻¹ • Measure.count := by
  refine Measure.ext_of_singleton fun x => ?_
  rw [sing_uniform_of_transitive (G := G) μ htrans x]
  simp [Measure.smul_apply, one_div]

end Brockian.EquidistributionUniformity

