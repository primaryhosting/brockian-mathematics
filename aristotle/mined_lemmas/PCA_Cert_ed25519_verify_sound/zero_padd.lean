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

theorem zero_padd (p : C.Pt) : C.padd C.pzero p = p := by
  rw [C.padd_comm, C.padd_zero]

/-- Additive inverses in the point group are unique. -/
