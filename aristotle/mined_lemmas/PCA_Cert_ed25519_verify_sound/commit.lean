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

def commit (r : C.Scalar) : C.Pt := C.act r C.B

/-- The Ed25519 verification equation `[S] B = R + [h] A`, where `A` is the public key,
`(R, S)` is the candidate signature and `h` is the hash scalar `H(R, A, M)`. -/
