import Mathlib

/-!
# Lagrange
Category: Frontier Wave 2 (deeper machinery)
Target: GroupTheory.lagrange
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


/-- **Lagrange's theorem**: for a finite group `G` and a subgroup `H`,
the cardinality of `H` divides the cardinality of `G`. -/
theorem GroupTheory.lagrange {G : Type*} [Fintype G] [Group G]
    (H : Subgroup G) [Fintype H] :
    Fintype.card H ∣ Fintype.card G := by
  simpa only [Nat.card_eq_fintype_card] using Subgroup.card_subgroup_dvd_card H

