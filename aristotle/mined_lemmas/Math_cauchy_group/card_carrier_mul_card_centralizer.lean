/-
# Cauchy Group
Category: Pure Mathematics
Target: Math.cauchy_group
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Math

open MulAction Subgroup

/-- From an element whose order is divisible by `p` we get an element of order exactly `p`. -/

theorem card_carrier_mul_card_centralizer {G : Type*} [Group G] [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier *
      Nat.card (Subgroup.centralizer ({g} : Set G)) = Nat.card G := by
  have hcar : Nat.card (ConjClasses.mk g).carrier =
      (Subgroup.centralizer ({g} : Set G)).index := by
    rw [← ConjAct.orbit_eq_carrier_conjClasses]
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct G) g)]
    rw [Subgroup.centralizer_eq_comap_stabilizer]
    rw [Subgroup.index_comap_of_surjective _ (ConjAct.toConjAct (G := G)).surjective]
    rfl
  rw [hcar, mul_comm, Subgroup.card_mul_index]

/-- If no proper subgroup of `G` has order divisible by `p`, then `p` divides the order of
the center of `G`.  This is the class-equation step of Cauchy's theorem. -/
