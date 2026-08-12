/-
# Ed 25519 Verify Sound
Category: Proof-Carrying Apps
Target: PCA.Cert.ed25519_verify_sound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## An abstract model of Ed25519 signature verification

We model the group in which Ed25519 operates as an additive commutative group `G`
which is a module over `ZMod L` (the scalar field, `L` being the prime order of the
base point subgroup), together with a distinguished base point `B` whose associated
"scalar multiple" map `c ↦ c • B` is injective — i.e. `B` generates a subgroup of
exact order `L`, so discrete logarithms with respect to `B` are unique.

A key pair is `(a, A)` with `A = a • B`. A signature on a message `m` with nonce `r`
is the pair `(R, S) = (r • B, r + H(R, A, m) * a)`, where `H` is an arbitrary hash
function into the scalar field. Verification of `(R, S)` against `A` and `m` is the
group equation `S • B = R + H(R, A, m) • A`.

The main theorem `PCA.Cert.ed25519_verify_sound` states that verification is both
*sound* and *complete* for this model: for a public key `A = a • B` and a commitment
`R = r • B`, the verification equation holds **iff** the scalar `S` is exactly the one
produced by the signing algorithm.  Completeness gives that honestly produced
signatures verify; soundness gives that no other scalar can ever be accepted.

The mathematical content is the injectivity of `c ↦ c • B`; the group-theoretic
rearrangement is `add_smul`/`mul_smul` (Mathlib), and the final step is
`Function.Injective.eq_iff` (Mathlib).
-/

namespace PCA.Cert

variable {L : ℕ} {G : Type*} {Msg : Type*} [AddCommGroup G] [Module (ZMod L) G]

/-- The verification predicate of the Ed25519 model: the signature `(R, S)` is accepted
for public key `A` and message `m` when `S • B = R + H(R, A, m) • A`. -/
def Verify (B : G) (hash : G → G → Msg → ZMod L)
    (A : G) (m : Msg) (sig : G × ZMod L) : Prop :=
  sig.2 • B = sig.1 + hash sig.1 A m • A

/-- The public key associated with a secret scalar `a`. -/
def pubKey (B : G) (a : ZMod L) : G := a • B

/-- The signing algorithm: with secret scalar `a`, nonce `r` and message `m`, the
signature is `(r • B, r + H(r • B, a • B, m) * a)`. -/
def sign (B : G) (hash : G → G → Msg → ZMod L)
    (a r : ZMod L) (m : Msg) : G × ZMod L :=
  (r • B, r + hash (r • B) (pubKey B a) m * a)

/-- **Soundness and completeness of Ed25519 verification** (abstract model).

For a base point `B` generating a subgroup of order `L` (expressed by injectivity of
`c ↦ c • B`), a public key `A = a • B` and a commitment `R = r • B`, the verification
equation `S • B = R + H(R, A, m) • A` holds if and only if `S` is exactly the scalar
computed by the signing algorithm, `S = r + H(R, A, m) * a`.

The forward direction is soundness (only the honest scalar is accepted); the backward
direction is completeness (honest signatures always verify). -/
theorem ed25519_verify_sound
    (B : G) (hB : Function.Injective (fun c : ZMod L => c • B))
    (hash : G → G → Msg → ZMod L) (a r S : ZMod L) (m : Msg) :
    Verify B hash (pubKey B a) m (r • B, S) ↔
      S = r + hash (r • B) (pubKey B a) m * a := by
  have key : (r • B : G) + hash (r • B) (pubKey B a) m • pubKey B a
      = (r + hash (r • B) (pubKey B a) m * a) • B := by
    simp [pubKey, add_smul, mul_smul]
  unfold Verify
  simp only [key]
  exact hB.eq_iff

/-- **Completeness**: an honestly generated signature always verifies. -/
theorem ed25519_sign_verify
    (B : G) (hash : G → G → Msg → ZMod L) (a r : ZMod L) (m : Msg) :
    Verify B hash (pubKey B a) m (sign B hash a r m) := by
  simp [Verify, sign, pubKey, add_smul, mul_smul]

/-- **Uniqueness of accepted signatures**: for a fixed commitment `R = r • B`, at most
one scalar `S` is accepted, namely the one produced by `sign`. -/
theorem ed25519_verify_unique
    (B : G) (hB : Function.Injective (fun c : ZMod L => c • B))
    (hash : G → G → Msg → ZMod L) (a r S : ZMod L) (m : Msg)
    (h : Verify B hash (pubKey B a) m (r • B, S)) :
    (r • B, S) = sign B hash a r m := by
  have := (ed25519_verify_sound B hB hash a r S m).mp h
  simp [sign, this]

/-- Sanity check: the hypotheses of `ed25519_verify_sound` are satisfiable, e.g. by the
cyclic group `ZMod L` with base point `1`. -/
example (L : ℕ) [NeZero L] :
    Function.Injective (fun c : ZMod L => c • (1 : ZMod L)) := by
  intro x y h
  simpa using h

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

