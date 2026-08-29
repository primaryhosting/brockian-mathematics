/-!
# Ed 25519 Verify Sound
Category: Proof-Carrying Apps
Target: PCA.Cert.ed25519_verify_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
## An abstract model of Ed25519 signature verification

We model the Ed25519 signature scheme inside the prime-order subgroup of the
twisted Edwards curve `edwards25519`.  The group is kept abstract: it is any
commutative group `G` (class `PCA.Cert.PointGroup`) together with a base point
`B` whose additive order is the Ed25519 group order

  `ell = 2^252 + 27742317777372353535851937790883648493`.

Scalars are natural numbers acting on points by repeated addition
(`PCA.Cert.PointGroup.nsmul`).  The challenge hash `H` (computing
`k = H(R, A, M)`) is abstract as well: no property of it is assumed, so all the
results below hold for every instantiation of the hash.

Main results:

* `PCA.Cert.ed25519_verify_complete` -- honestly produced signatures verify;
* `PCA.Cert.ed25519_verify_sound`    -- conversely, if the verification equation
  holds for the public key `A = s * B` and the signature's commitment is
  `R = r * B`, then the signature is *exactly* the honest signature for the
  secret scalar `s`, nonce `r` and message `m`.  In other words the verifier
  accepts no pair `(R, S)` other than the unique one prescribed by the Ed25519
  signing equation `S = r + H(R, A, M) * s  (mod ell)`.

The development is self-contained: it depends only on the Lean 4 core library.
-/

namespace PCA.Cert

/-- The order of the prime-order subgroup of `edwards25519` used by Ed25519. -/

theorem ed25519_verify_sound_Zell (H : Zell → Zell → Message → Nat) (s r : Nat)
    (m : Message) (sig : Signature Zell) (hR : sig.R = nsmul r Zell.gen)
    (hv : verify H Zell.gen (publicKey Zell.gen s) m sig) :
    sig = sign H Zell.gen s r m :=
  ed25519_verify_sound Zell.gen_order Zell.gen_order_min H s r m sig hR hv

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

