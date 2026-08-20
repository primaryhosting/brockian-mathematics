import Mathlib

/-!
# Lagrange Subgroup
Category: Pure Mathematics
Target: Math.lagrange_subgroup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Lagrange's theorem**: the order of a subgroup of a finite group divides the
order of the group.  Here the orders are expressed as `Fintype.card`.

This follows from Mathlib's `Subgroup.card_subgroup_dvd_card`. -/

theorem lagrange_subgroup_natCard {G : Type*} [Group G] (H : Subgroup G) :
    Nat.card H ∣ Nat.card G :=
  H.card_subgroup_dvd_card

end Math

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

