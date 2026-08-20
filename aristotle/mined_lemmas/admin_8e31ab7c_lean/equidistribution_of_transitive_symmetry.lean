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

If a group `G` acts transitively on a finite nonempty type `X`, then every `G`-invariant
weighting of `X` whose total mass is `1` is the uniform weighting `x ↦ 1 / |X|`.

This is the "equidistribution uniformity" principle: transitive symmetry forces uniformity.

The main statement `Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry`
is unconditional: the uniformity conclusion is derived, not assumed.
-/

namespace Brockian
namespace EquidistributionUniformity

open Finset

variable {G X : Type*} [Group G] [MulAction G X]

/-- An invariant weight function is constant along orbits; under a transitive action it is
therefore globally constant. -/

theorem equidistribution_of_transitive_symmetry [Fintype X] [Nonempty X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (w : X → ℝ) (hsum : ∑ x : X, w x = 1)
    (hinv : ∀ (g : G) (x : X), w (g • x) = w x) :
    ∀ x : X, w x = (Fintype.card X : ℝ)⁻¹ := by
  have hconst : ∀ x y : X, w x = w y := const_of_transitive_invariant w htrans hinv
  intro x
  have hcard : (0 : ℝ) < (Fintype.card X : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr ‹Nonempty X›
  have hs : ∑ y : X, w y = (Fintype.card X : ℝ) * w x := by
    rw [Finset.sum_congr rfl (fun y _ => hconst y x)]
    simp [Finset.card_univ, mul_comm]
  rw [hs] at hsum
  field_simp
  linarith [hsum]

/-- Measure-theoretic form: a `G`-invariant probability mass function on a finite type with a
transitive `G`-action is the uniform distribution. -/
