/-
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.EquidistributionUniformity

/-- A weight function that is invariant under a transitive group action is constant. -/

theorem constant_of_transitive_symmetry
    {G X M : Type*} [Group G] [MulAction G X]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (f : X → M) (hinv : ∀ (g : G) (x : X), f (g • x) = f x) :
    ∀ x y : X, f x = f y := by
  intro x y
  obtain ⟨g, hg⟩ := htrans x y
  rw [← hg, hinv]

/-- **Equidistribution of transitive symmetry.**  If a group `G` acts transitively on a
nonempty finite type `X` and `f : X → ℝ` is a `G`-invariant probability weight, then `f`
is the uniform distribution: `f x = 1 / card X` for every `x`.

This is stated unconditionally: no constancy (or uniformity) hypothesis is assumed, it is
derived from transitivity and invariance. -/
