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

theorem verify_extract (a h S : C.Scalar) (R : C.Pt)
    (hv : Verify C (pubkey C a) R h S) :
    R = C.act (C.ssub S (C.smul h a)) C.B := by
  rw [C.act_ssub]
  rw [Verify, pubkey, ← C.act_smul] at hv
  rw [hv, C.padd_assoc, C.padd_neg, C.padd_zero]

/--
**Ed25519 verification is sound and complete** with respect to the signing algorithm.

For a key pair with secret scalar `a` and a nonce `r`, the verification equation accepts the
candidate signature `([r] B, S)` on the message `m` *if and only if* `([r] B, S)` is exactly
the signature produced by the signing algorithm on `(a, r, m)`.

The forward implication is soundness: nothing except the honest signature is accepted, so an
accepting signature witnesses the relation `S = r + H(R, A, M) * a`. The backward implication
is completeness: the honest signature is always accepted.
-/
