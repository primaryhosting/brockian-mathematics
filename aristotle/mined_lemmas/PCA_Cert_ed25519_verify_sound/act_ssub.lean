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

theorem act_ssub (a b : C.Scalar) (p : C.Pt) :
    C.act (C.ssub a b) p = C.padd (C.act a p) (C.pneg (C.act b p)) := by
  rw [ssub, C.act_sadd, C.act_sneg]

end Curve

variable (C : Curve)

/-- The public key associated with the secret scalar `a`, namely `A = [a] B`. -/
