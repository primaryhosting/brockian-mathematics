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

theorem equidistribution_of_transitive_symmetry [Fintype X]
    [MulAction.IsPretransitive G X]
    (w : X → ℝ) (hinv : ∀ (g : G) (x : X), w (g • x) = w x)
    (hsum : ∑ y, w y = 1) (x : X) :
    w x = (Fintype.card X : ℝ)⁻¹ := by
  have hcard : (Fintype.card X : ℝ) ≠ 0 := by
    have : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨x⟩
    positivity
  have hconst : ∑ y, w y = (Fintype.card X : ℝ) * w x := by
    rw [Finset.sum_congr rfl (fun y _ => weight_const_of_transitive hinv y x)]
    simp [Finset.card_univ, mul_comm]
  rw [hconst] at hsum
  field_simp at hsum ⊢
  linarith [hsum]

/-- Subset form of equidistribution: an invariant normalized weight assigns to a finite
set `S ⊆ X` the mass `|S| / |X|`. -/
