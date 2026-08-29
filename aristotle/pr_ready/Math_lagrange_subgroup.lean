/-!
# Lagrange Subgroup
Category: Pure Mathematics
Target: Math.lagrange_subgroup
Statement: The order of a subgroup divides the order of a finite group.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Lagrange Subgroup
Category: Pure Mathematics
Target: Math.lagrange_subgroup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Lagrange Subgroup
Category: Pure Mathematics
Target: Math.lagrange_subgroup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Lagrange's theorem**: the order of a subgroup of a finite group divides the
order of the group. Stated with `Fintype.card`; the proof cites Mathlib's
`Subgroup.card_subgroup_dvd_card` (phrased with `Nat.card`). -/
theorem lagrange_subgroup {G : Type*} [Group G] [Fintype G] (H : Subgroup G)
    [Fintype H] : Fintype.card H ∣ Fintype.card G := by
  simpa [Nat.card_eq_fintype_card] using Subgroup.card_subgroup_dvd_card H

end Math

