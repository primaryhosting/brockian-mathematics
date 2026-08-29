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

theorem act_sneg (a : C.Scalar) (p : C.Pt) : C.act (C.sneg a) p = C.pneg (C.act a p) := by
  refine C.pneg_unique ?_
  rw [← C.act_sadd, C.sadd_neg, C.act_szero]

/-- The action turns scalar subtraction into point subtraction. -/
