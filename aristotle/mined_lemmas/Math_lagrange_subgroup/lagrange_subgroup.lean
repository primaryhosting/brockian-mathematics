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

theorem lagrange_subgroup {G : Type*} [Group G] [Fintype G] (H : Subgroup G) [Fintype H] :
    Fintype.card H ∣ Fintype.card G := by
  simpa [Nat.card_eq_fintype_card] using H.card_subgroup_dvd_card

/-- Version of Lagrange's theorem for `Nat.card`, valid for any group (with the
convention `Nat.card = 0` for infinite types). -/
