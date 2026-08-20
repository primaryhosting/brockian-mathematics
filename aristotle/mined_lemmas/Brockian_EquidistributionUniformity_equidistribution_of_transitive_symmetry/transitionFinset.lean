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
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.EquidistributionUniformity

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]

/-- The fiber over `x` of the orbit map `g ↦ g • z`, as a `Finset` of group elements. -/

def transitionFinset [Fintype G] [DecidableEq X] (z x : X) : Finset G :=
  Finset.univ.filter fun g : G => g • z = x

/-- Every nonempty fiber of the orbit map `g ↦ g • z` is a left coset of the stabilizer of `z`,
hence has exactly `|stabilizer G z|` elements. -/
