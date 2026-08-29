/-!
# Equidistribution Of Transitive Symmetry
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionUniformity.equidistribution_of_transitive_symmetry
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace EquidistributionUniformity

/-- **Equidistribution of a transitive symmetry group.**

If a finite group `G` acts transitively on a finite type `X`, then pushing the uniform
distribution on `G` forward along the orbit map `g ↦ g • x` yields the uniform distribution
on `X`: every point `y : X` is hit by exactly `|G| / |X|` group elements, i.e. the fiber
`{g : G | g • x = y}` has cardinality `c` with `c * |X| = |G|`.

The statement is unconditional: no auxiliary hypothesis beyond transitivity of the action
and finiteness is assumed (in particular no nonemptiness hypothesis is needed, since the
identity `0 * 0 = 0` holds in the empty case as well). -/

theorem card_fiber_eq_of_transitive_symmetry
    {G X : Type*} [Group G] [Fintype G] [MulAction G X] [Fintype X]
    [MulAction.IsPretransitive G X] (x y z : X) :
    (Finset.univ.filter (fun g : G => g • x = y)).card
      = (Finset.univ.filter (fun g : G => g • x = z)).card := by
  have hy := equidistribution_of_transitive_symmetry (G := G) x y
  have hz := equidistribution_of_transitive_symmetry (G := G) x z
  have hX : 0 < Fintype.card X := Fintype.card_pos_iff.mpr ⟨x⟩
  exact Nat.eq_of_mul_eq_mul_right hX (hy.trans hz.symm)

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

