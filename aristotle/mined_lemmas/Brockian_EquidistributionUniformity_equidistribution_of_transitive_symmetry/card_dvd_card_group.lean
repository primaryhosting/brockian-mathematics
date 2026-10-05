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

/-
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of Transitive Symmetry

If a group `G` acts transitively on a set `X`, then the group elements are equidistributed over
the points of `X`: for a fixed base point `x`, each target point `y` is hit by exactly
`Nat.card G / Nat.card X` group elements.  The equidistribution property, which is elsewhere
taken as a hypothesis, is proved here outright from transitivity via the orbit-stabilizer
theorem.
-/

namespace Brockian
namespace EquidistributionUniformity

open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

/-- The *transporter* from `x` to `y`: the set of symmetries carrying `x` to `y`. -/

theorem card_dvd_card_group [IsPretransitive G X] (x : X) :
    Nat.card X ∣ Nat.card G :=
  ⟨Nat.card (transporter G x x), (equidistribution_of_transitive_symmetry x x).symm⟩

/-- The explicit uniform count, for a finite group: every point receives exactly
`Nat.card G / Nat.card X` symmetries. -/
