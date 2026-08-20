/-!
# Lagrange
Category: Frontier Wave 2 (deeper machinery)
Target: GroupTheory.lagrange
Statement: Lagrange's theorem: for a finite group G and a subgroup H, the cardinality of H divides the cardinality of G. State: for [Fintype G] [Group G] (H : Subgroup G) [Fintype H], Fintype.card H divides Fintype.card G. (Use Mathlib's Subgroup.card_subgroup_dvd_card.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace GroupTheory

/-- **Lagrange's theorem**: for a finite group `G` and a subgroup `H`, the cardinality of `H`
divides the cardinality of `G`. -/
theorem lagrange {G : Type*} [Fintype G] [Group G] (H : Subgroup G) [Fintype H] :
    Fintype.card H ∣ Fintype.card G :=
  by simpa [Nat.card_eq_fintype_card] using Subgroup.card_subgroup_dvd_card H

end GroupTheory

