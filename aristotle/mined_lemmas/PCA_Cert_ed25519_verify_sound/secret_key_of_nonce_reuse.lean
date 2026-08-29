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

theorem secret_key_of_nonce_reuse (B A R : G) (ell : ℕ) [Fact (Nat.Prime ell)]
    (hell : addOrderOf B = ell) (a r h₁ h₂ s₁ s₂ : ℤ) (hA : A = a • B) (hR : R = r • B)
    (hne : (h₁ : ZMod ell) ≠ (h₂ : ZMod ell))
    (hv₁ : Verify B A R h₁ s₁) (hv₂ : Verify B A R h₂ s₂) :
    (a : ZMod ell) = ((s₁ : ZMod ell) - (s₂ : ZMod ell)) / ((h₁ : ZMod ell) - (h₂ : ZMod ell)) := by
  have e₁ := (ed25519_verify_sound B A R ell hell a r h₁ s₁ hA hR).1 hv₁
  have e₂ := (ed25519_verify_sound B A R ell hell a r h₂ s₂ hA hR).1 hv₂
  have hsub : (h₁ : ZMod ell) - (h₂ : ZMod ell) ≠ 0 := sub_ne_zero_of_ne hne
  field_simp
  rw [e₁, e₂]
  ring

end PCA.Cert

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

