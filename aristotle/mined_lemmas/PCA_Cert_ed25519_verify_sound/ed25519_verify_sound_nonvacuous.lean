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

theorem ed25519_verify_sound_nonvacuous {L : ℕ} [Fact (Nat.Prime L)] {Msg : Type*}
    (H : ZMod L → ZMod L → Msg → ZMod L) (s : ZMod L) (m : Msg) (R S : ZMod L) :
    verify H (1 : ZMod L) (publicKey (1 : ZMod L) s) m (R, S) ↔
      ∃ r : ZMod L, R = r • (1 : ZMod L) ∧
        S = r + H R (publicKey (1 : ZMod L) s) m * s :=
  ed25519_verify_sound H 1 one_ne_zero (fun P => ⟨P, by simp⟩) s m R S

end Ed25519

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

