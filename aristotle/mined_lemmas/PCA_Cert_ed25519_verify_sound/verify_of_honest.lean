/-
# Ed 25519 Verify Sound
Category: Proof-Carrying Apps
Target: PCA.Cert.ed25519_verify_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ed 25519 Verify Sound
Category: Proof-Carrying Apps
Target: PCA.Cert.ed25519_verify_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Cert

variable {G : Type*} [AddCommGroup G]

/-- The Ed25519 verification equation, in additive group notation.

`B` is the base point, `A` the public key, `R` the signature nonce point, `h` the challenge
scalar (in the real scheme, `h = SHA-512(R ‖ A ‖ M)` reduced mod the group order) and `s` the
signature scalar.  A signature `(R, s)` on the challenge `h` is accepted exactly when
`s • B = R + h • A`. -/

theorem verify_of_honest (B A R : G) (ell : ℕ) (hell : addOrderOf B = ell)
    (a r h s : ℤ) (hA : A = a • B) (hR : R = r • B)
    (hs : (s : ZMod ell) = (r : ZMod ell) + (h : ZMod ell) * (a : ZMod ell)) :
    Verify B A R h s :=
  (ed25519_verify_sound B A R ell hell a r h s hA hR).2 hs

/-- Soundness, in contrapositive form: a signature scalar that differs from the honest Schnorr
response modulo the group order is rejected. -/
