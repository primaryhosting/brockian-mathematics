/-!
# Reprove Matches Iff Untampered
Category: Proof-Carrying Apps
Target: PCA.Cert.reprove_matches_iff_untampered
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Cert

/-! ## Arithmetic: an injective pairing function on `Nat` -/

/-- Szudzik-style pairing function. -/

theorem encList_inj : ∀ {l l' : List Nat}, encList l = encList l' → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [encList] at h
  | _ :: _, [], h => by simp [encList] at h
  | x :: xs, y :: ys, h => by
      simp only [encList, Nat.add_right_cancel_iff] at h
      obtain ⟨hx, hxs⟩ := pairNat_inj h
      rw [hx, encList_inj hxs]

