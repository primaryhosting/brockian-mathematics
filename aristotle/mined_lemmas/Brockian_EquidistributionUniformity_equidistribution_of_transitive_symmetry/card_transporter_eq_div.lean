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

theorem card_transporter_eq_div [Finite G] [IsPretransitive G X] (x y : X) :
    Nat.card (transporter G x y) = Nat.card G / Nat.card X := by
  have hX : Nat.card X ≠ 0 := by
    have : Finite X := by
      have : Function.Surjective (fun g : G => g • x) := fun y =>
        IsPretransitive.exists_smul_eq (M := G) x y
      exact Finite.of_surjective _ this
    exact Nat.card_ne_zero.mpr ⟨⟨x⟩, this⟩
  rw [← equidistribution_of_transitive_symmetry (G := G) x y,
    Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hX)]

end EquidistributionUniformity
end Brockian

