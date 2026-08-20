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

theorem card_transitionFinset_eq_card_transitionFinset [Fintype G] [Fintype X] [DecidableEq X]
    [MulAction.IsPretransitive G X] (z x y : X) :
    (transitionFinset G z x).card = (transitionFinset G z y).card := by
  have hx := equidistribution_of_transitive_symmetry G z x
  have hy := equidistribution_of_transitive_symmetry G z y
  have hX : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨x⟩
  exact Nat.eq_of_mul_eq_mul_right hX (hx.trans hy.symm)

end Brockian.EquidistributionUniformity

