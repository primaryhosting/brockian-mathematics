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

/-!
# Sing Uniform Of Transitive
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.sing_uniform_of_transitive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Brockian.EquidistributionUniformity

variable {G X : Type*} [Group G] [MulAction G X]

/-- The set of group elements carrying a fixed base point `x` to the point `y`:
the "fiber" of the orbit map `g ↦ g • x` over `y`. -/

def fiber (x y : X) : Set G := {g : G | g • x = y}

/-- For a transitive action, all fibers of the orbit map `g ↦ g • x` are in bijection:
translating by an element `h` with `h • y = z` is a bijection from the fiber over `y`
to the fiber over `z`. -/
