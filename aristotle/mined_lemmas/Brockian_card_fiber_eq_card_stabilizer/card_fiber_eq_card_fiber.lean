import Mathlib

/-!
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 800000

namespace Brockian
namespace EquidistributionUniformity

/-- **Fibres of a transitive action are cosets of a stabiliser.**

If a group `G` acts transitively on `X` and `g₀ • x = y`, then the set of group elements
carrying `x` to `y` is in bijection with the stabiliser of `x`; in particular the fibres of
the orbit map `g ↦ g • x` all have the same cardinality. -/

theorem card_fiber_eq_card_fiber
    {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [MulAction.IsPretransitive G X] (x y y' : X) :
    {g : G | g • x = y}.toFinset.card = {g : G | g • x = y'}.toFinset.card := by
  have h1 := equidistribution_of_transitive_symmetry (G := G) x y
  have h2 := equidistribution_of_transitive_symmetry (G := G) x y'
  have hX : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨x⟩
  exact Nat.eq_of_mul_eq_mul_right hX (h1.trans h2.symm)

end EquidistributionUniformity
end Brockian

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

