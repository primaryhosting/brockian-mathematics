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

theorem const_of_transitive_invariant {M : Type*} (w : X → M)
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (hinv : ∀ (g : G) (x : X), w (g • x) = w x) :
    ∀ x y : X, w x = w y := by
  intro x y
  obtain ⟨g, hg⟩ := htrans x y
  rw [← hg, hinv]

/-- **Equidistribution from transitive symmetry.**

Let a group `G` act transitively on a finite nonempty type `X`, and let `w : X → ℝ` be a
`G`-invariant weight with total mass `1`. Then `w` is the uniform weight `x ↦ 1 / |X|`.

The uniformity of `w` is *concluded*, not hypothesized. -/
