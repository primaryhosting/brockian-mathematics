/-
# Ed 25519 Verify Sound
Category: Proof-Carrying Apps
Target: PCA.Cert.ed25519_verify_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace PCA.Cert

/-!
## An abstract model of Ed25519 signature verification

Ed25519 signatures live in the prime-order subgroup `⟨B⟩` of the Edwards curve
`edwards25519`, where `B` is the standard base point and `L` is the (prime) order
of `B`.  Since that subgroup is a one-dimensional vector space over `ZMod L`, we
model the situation abstractly:

* `G` is an additive commutative group which is a module over `ZMod L`
  (`L` prime), i.e. the prime-order subgroup;
* `B : G` is the base point, assumed nonzero and generating (`hgen`);
* the hash function is an arbitrary function `H : G → G → Msg → ZMod L`
  (no cryptographic assumption on `H` is needed: the statements below are
  *algebraic* soundness/completeness of the verification equation).

A secret scalar `s : ZMod L` has public key `A = s • B`.  A signature on a
message `m` with nonce `r` is the pair `(r • B, r + H (r•B) A m * s)`, and
verification of `(R, S)` against `A` checks `S • B = R + H R A m • A`.
-/

section Ed25519

variable {L : ℕ} [Fact (Nat.Prime L)] {G : Type*} [AddCommGroup G] [Module (ZMod L) G]
variable {Msg : Type*}

/-- The public key associated with a secret scalar `s`, w.r.t. base point `B`. -/

theorem smul_base_injective {B : G} (hB : B ≠ 0) :
    Function.Injective (fun c : ZMod L => c • B) := by
  intro c d h
  have h' : c • B = d • B := h
  have h0 : (c - d) • B = 0 := by rw [sub_smul, h', sub_self]
  rcases smul_eq_zero.1 h0 with h1 | h1
  · exact sub_eq_zero.1 h1
  · exact absurd h1 hB

/-- **Completeness**: an honestly generated Ed25519 signature always verifies. -/
