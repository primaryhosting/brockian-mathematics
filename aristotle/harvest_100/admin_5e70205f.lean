import Mathlib

/-!
# Lagrange Subgroup
Category: Pure Mathematics
Target: Math.lagrange_subgroup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every other command, including
-- module documentation comments (`/-! ... -/`). The requested header is therefore
-- placed immediately after the single `import Mathlib` line, verbatim.

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

/-- **Lagrange's theorem**: the order of a subgroup of a finite group divides the
order of the group.

The Mathlib ingredient used is `Subgroup.card_subgroup_dvd_card`
(`Mathlib/GroupTheory/Coset/Card.lean`), which gives `Nat.card H ∣ Nat.card G`. -/
theorem lagrange_subgroup {G : Type*} [Group G] [Fintype G] (H : Subgroup G)
    [Fintype H] : Fintype.card H ∣ Fintype.card G := by
  have h : Nat.card H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
  simpa [Nat.card_eq_fintype_card] using h

/-- Lagrange's theorem in `Nat.card` form, valid for an arbitrary group (with the
convention `Nat.card = 0` for infinite types). -/
theorem lagrange_subgroup_natCard {G : Type*} [Group G] (H : Subgroup G) :
    Nat.card H ∣ Nat.card G :=
  Subgroup.card_subgroup_dvd_card H

end Math

#print axioms Math.lagrange_subgroup
#print axioms Math.lagrange_subgroup_natCard

