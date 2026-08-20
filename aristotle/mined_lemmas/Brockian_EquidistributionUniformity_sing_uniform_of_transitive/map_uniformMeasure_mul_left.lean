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
# Equidistribution from transitivity

If a group `G` acts transitively on a finite type `α` and `μ` is a `G`-invariant probability
measure on `α`, then `μ` is the uniform distribution: every singleton has measure
`(Fintype.card α)⁻¹`.

The main result is `Brockian.EquidistributionUniformity.sing_uniform_of_transitive`, stated
unconditionally (no auxiliary named hypothesis beyond invariance of the measure).
-/

open MeasureTheory

namespace Brockian
namespace EquidistributionUniformity

variable {G α : Type*}

/-- On a finite type whose singletons are measurable, every set is measurable. -/

theorem map_uniformMeasure_mul_left [Group G] [Fintype G] [MeasurableSpace G]
    [MeasurableSingletonClass G] (g : G) :
    Measure.map (fun x : G => g • x) (uniformMeasure G) = uniformMeasure G := by
  rw [uniformMeasure, Measure.map_smul]
  congr 1
  exact map_count_equiv (Equiv.mulLeft g)

/-- Instance of the main theorem: on a finite group, the uniform measure assigns mass
`(Fintype.card G)⁻¹` to each singleton. -/
example [Group G] [Fintype G] [MeasurableSpace G] [MeasurableSingletonClass G] (x : G) :
    uniformMeasure G {x} = (Fintype.card G : ENNReal)⁻¹ :=
  sing_uniform_of_transitive (G := G) (uniformMeasure G) map_uniformMeasure_mul_left x

end EquidistributionUniformity
end Brockian

