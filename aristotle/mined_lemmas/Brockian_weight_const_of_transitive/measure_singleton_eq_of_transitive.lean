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

theorem measure_singleton_eq_of_transitive [MulAction.IsPretransitive G X]
    (mu : Measure X) [SMulInvariantMeasure G X mu] (x y : X) :
    mu {x} = mu {y} := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G x y
  have h := SMulInvariantMeasure.measure_preimage_smul (μ := mu) g
    (measurableSet_singleton y)
  have hpre : (fun z : X => g • z) ⁻¹' {y} = {x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      have : g • z = g • x := by rw [hz, hg]
      exact MulAction.injective g this
    · rintro rfl
      exact hg
  rwa [hpre] at h

/-- **Uniformity of invariant probability measures.**
A `G`-invariant probability measure on a finite `G`-set with transitive action is the
uniform measure: each singleton has mass `1 / |X|`. -/
