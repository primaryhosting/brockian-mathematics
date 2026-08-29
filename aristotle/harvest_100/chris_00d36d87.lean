/-
# Lagrange Subgroup
Category: Pure Mathematics
Target: Math.lagrange_subgroup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lagrange Subgroup
Category: Pure Mathematics
Target: Math.lagrange_subgroup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

/-- **Lagrange's theorem**: the order of a subgroup divides the order of a finite group.

The proof is the classical coset argument: `G` is partitioned into the left cosets of `H`,
each of which is in bijection with `H`, so `|G| = [G : H] * |H|`.  Here this is packaged
via the group-theoretic bijection `G ≃ (G ⧸ H) × H`. -/
theorem lagrange_subgroup {G : Type*} [Group G] [Fintype G] (H : Subgroup G) :
    Fintype.card H ∣ Fintype.card G := by
  classical
  have e : G ≃ (G ⧸ H) × H := Subgroup.groupEquivQuotientProdSubgroup (s := H)
  have hcard : Fintype.card G = Fintype.card (G ⧸ H) * Fintype.card H := by
    have := Fintype.card_congr e
    simpa using this
  exact ⟨Fintype.card (G ⧸ H), by rw [hcard, Nat.mul_comm]⟩

end Math

