/-!
# Sperner Card Le
Category: Brockian External
Target: Brockian.Sperner.sperner_card_le
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.Sperner
/-- Sperner's theorem: an antichain in the Boolean lattice on a finite type α has at most
    C(|α|, ⌊|α|/2⌋) members. -/
theorem sperner_card_le {α : Type*} [Fintype α] [DecidableEq α]
    (𝒜 : Finset (Finset α)) (h : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    𝒜.card ≤ (Fintype.card α).choose (Fintype.card α / 2) := by
  exact h.sperner
end Brockian.Sperner

