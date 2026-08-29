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

theorem verify_iff_scalar (a r h S : C.Scalar) :
    Verify C (pubkey C a) (commit C r) h S ↔ S = C.sadd r (C.smul h a) := by
  have key : C.act (C.sadd r (C.smul h a)) C.B
      = C.padd (commit C r) (C.act h (pubkey C a)) := by
    rw [C.act_sadd, C.act_smul, commit, pubkey]
  constructor
  · intro hv
    refine C.base_injective _ _ ?_
    rw [hv, key]
  · intro hv
    rw [Verify, hv, key]

/-- Completeness: an honestly produced Ed25519 signature always verifies. -/
