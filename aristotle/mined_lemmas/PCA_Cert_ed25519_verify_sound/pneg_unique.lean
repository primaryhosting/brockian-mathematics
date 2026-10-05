/-!
# Ed 25519 Verify Sound
Category: Proof-Carrying Apps
Target: PCA.Cert.ed25519_verify_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Cert

/-- The Ed25519 group order
`ℓ = 2^252 + 27742317777372353535851937790883648493`,
the (prime) order of the standard base point of `edwards25519`. -/

theorem pneg_unique {p q : C.Pt} (h : C.padd p q = C.pzero) : q = C.pneg p := by
  have h1 : C.padd (C.pneg p) (C.padd p q) = C.padd (C.pneg p) C.pzero := by rw [h]
  rw [← C.padd_assoc, C.padd_zero, C.padd_comm (C.pneg p) p, C.padd_neg, C.zero_padd] at h1
  exact h1

/-- A negated scalar acts as the negation of the action. -/
