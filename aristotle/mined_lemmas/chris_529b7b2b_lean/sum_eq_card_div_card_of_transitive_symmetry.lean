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

theorem sum_eq_card_div_card_of_transitive_symmetry [Fintype X]
    [MulAction.IsPretransitive G X]
    (w : X → ℝ) (hinv : ∀ (g : G) (x : X), w (g • x) = w x)
    (hsum : ∑ y, w y = 1) (S : Finset X) :
    ∑ y ∈ S, w y = (S.card : ℝ) / (Fintype.card X : ℝ) := by
  rw [Finset.sum_congr rfl
    (fun y _ => equidistribution_of_transitive_symmetry (G := G) w hinv hsum y)]
  simp [div_eq_mul_inv]

end Weights

section Measures

variable {G X : Type*} [Group G] [MulAction G X]
  [MeasurableSpace X] [MeasurableSingletonClass X] [Fintype X]

omit [Fintype X] in
/-- A `G`-invariant measure gives equal mass to all singletons when `G` acts transitively. -/
