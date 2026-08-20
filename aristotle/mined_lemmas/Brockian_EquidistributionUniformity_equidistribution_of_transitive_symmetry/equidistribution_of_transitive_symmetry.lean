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

theorem equidistribution_of_transitive_symmetry [Fintype G] [Fintype X] [DecidableEq X]
    [MulAction.IsPretransitive G X] (z x : X) :
    (transitionFinset G z x).card * Fintype.card X = Fintype.card G := by
  classical
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq G z x
  have hfib := card_transitionFinset_eq_card_stabilizer G z x g₀ hg₀
  have horb : Fintype.card (MulAction.orbit G z) = Fintype.card X := by
    rw [Fintype.card_congr (Equiv.setCongr (MulAction.orbit_eq_univ G z))]
    exact Fintype.card_congr (Equiv.Set.univ X)
  have hos :
      Fintype.card (MulAction.orbit G z) * Fintype.card (MulAction.stabilizer G z)
        = Fintype.card G :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group G z
  rw [hfib, Nat.card_eq_fintype_card, mul_comm, ← horb, hos]

/-- All fibers of the orbit map of a transitive action have the same cardinality. -/
