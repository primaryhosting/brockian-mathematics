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

def Verify (B A R : G) (h s : ℤ) : Prop := s • B = R + h • A

/-- **Soundness and completeness of Ed25519 verification.**

Let `B` be a point of order `ell`, let the public key be `A = a • B` and the nonce point be
`R = r • B`.  Then the verification equation holds *if and only if* the signature scalar `s`
is the honest Schnorr response `r + h * a` modulo the group order `ell`.

The forward direction is soundness: an accepted signature certifies that the scalar `s` is
determined by the discrete logarithms `a` of the public key and `r` of the nonce point, so no
other scalar can be substituted.  The backward direction is completeness: the honestly computed
response is always accepted. -/

theorem ed25519_verify_sound {G : Type*} [AddCommGroup G] (B A R : G) (ell : ℕ)
    (hell : addOrderOf B = ell) (a r h s : ℤ) (hA : A = a • B) (hR : R = r • B) :
    Verify B A R h s ↔ (s : ZMod ell) = (r : ZMod ell) + (h : ZMod ell) * (a : ZMod ell) := by
  subst hA hR hell
  have key : Verify B (a • B) (r • B) h s ↔ ((addOrderOf B : ℕ) : ℤ) ∣ (s - (r + h * a)) := by
    rw [addOrderOf_dvd_iff_zsmul_eq_zero, sub_smul, sub_eq_zero, add_smul, mul_smul, Verify]
  rw [key, show ((r : ZMod (addOrderOf B)) + (h : ZMod _) * (a : ZMod _))
      = ((r + h * a : ℤ) : ZMod (addOrderOf B)) by push_cast; ring,
    ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd, dvd_sub_comm]

/-- Completeness: the honestly generated response `s ≡ r + h * a` is always accepted. -/
