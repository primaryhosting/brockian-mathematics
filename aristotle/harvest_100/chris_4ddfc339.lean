import Mathlib

/-!
# Little-endian byte strings

Basic infrastructure for the Ed25519 certificate model: conversion between
natural numbers and fixed-width little-endian byte strings, together with the
round-trip and injectivity lemmas that make byte-level canonicality arguments
possible.
-/

namespace PCA

/-- Value of a little-endian byte string (least significant byte first). -/
def leToNat : List UInt8 → ℕ
  | [] => 0
  | b :: bs => b.toNat + 256 * leToNat bs

@[simp] theorem leToNat_nil : leToNat [] = 0 := rfl

@[simp] theorem leToNat_cons (b : UInt8) (bs : List UInt8) :
    leToNat (b :: bs) = b.toNat + 256 * leToNat bs := rfl

/-- The `k`-byte little-endian encoding of a natural number (truncating). -/
def natToLe (n : ℕ) : ℕ → List UInt8
  | 0 => []
  | k + 1 => UInt8.ofNat (n % 256) :: natToLe (n / 256) k

@[simp] theorem natToLe_zero (n : ℕ) : natToLe n 0 = [] := rfl

@[simp] theorem natToLe_succ (n k : ℕ) :
    natToLe n (k + 1) = UInt8.ofNat (n % 256) :: natToLe (n / 256) k := rfl

@[simp] theorem length_natToLe (n k : ℕ) : (natToLe n k).length = k := by
  induction k generalizing n with
  | zero => simp
  | succ k ih => simp [ih]

theorem toNat_ofNat_of_lt {n : ℕ} (h : n < 256) : (UInt8.ofNat n).toNat = n := by
  simp [Nat.mod_eq_of_lt h]

theorem leToNat_lt (bs : List UInt8) : leToNat bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      have hb : b.toNat < 256 := UInt8.toNat_lt b
      simp only [leToNat_cons, List.length_cons, pow_succ]
      omega

/-- Decoding the little-endian encoding of `n` recovers `n` modulo `256 ^ k`. -/
theorem leToNat_natToLe (n k : ℕ) : leToNat (natToLe n k) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
      have hmod : (UInt8.ofNat (n % 256)).toNat = n % 256 :=
        toNat_ofNat_of_lt (Nat.mod_lt _ (by norm_num))
      rw [natToLe_succ, leToNat_cons, hmod, ih]
      have : n % 256 ^ (k + 1) = n % 256 + 256 * (n / 256 % 256 ^ k) := by
        rw [pow_succ', Nat.mod_mul]
      omega

theorem leToNat_natToLe_of_lt {n k : ℕ} (h : n < 256 ^ k) : leToNat (natToLe n k) = n := by
  rw [leToNat_natToLe, Nat.mod_eq_of_lt h]

/-- Encoding the value of a byte string recovers the byte string. -/
theorem natToLe_leToNat (bs : List UInt8) : natToLe (leToNat bs) bs.length = bs := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      have hb : b.toNat < 256 := UInt8.toNat_lt b
      have h1 : (b.toNat + 256 * leToNat bs) % 256 = b.toNat := by omega
      have h2 : (b.toNat + 256 * leToNat bs) / 256 = leToNat bs := by omega
      simp only [List.length_cons, natToLe_succ, leToNat_cons, h1, h2, ih,
        List.cons.injEq, and_true]
      exact UInt8.ofNat_toNat

/-- Byte strings of equal length with equal values are equal. -/
theorem leToNat_injective {bs cs : List UInt8} (hlen : bs.length = cs.length)
    (h : leToNat bs = leToNat cs) : bs = cs := by
  have := natToLe_leToNat bs
  rw [h, hlen, natToLe_leToNat] at this
  exact this.symm

end PCA

import RequestProject.Engine

/-!
# A worked instance of the model

A small but complete instantiation of the certificate model, demonstrating that
the assumptions bundled in `PCA.Cert.Params` are satisfiable and that the
engine's grant predicate really does fire on honestly issued certificates
(so the soundness statements are not vacuous).
-/

namespace PCA
namespace Cert
namespace Demo

/-- A toy hash function. -/
def demoH : List UInt8 → List UInt8 → List UInt8 → ZMod 7 := fun _ _ _ => 3

/-- A toy instance of the scheme, over the prime-order group `ZMod 7`. -/
def demoParams : Params (ZMod 7) 7 := Params.ofZMod 7 (by norm_num) demoH

/-- A certificate for subject `[1]` granting access to resources `[2]` and `[3]`. -/
def demoCert : CapCert := ⟨[1], [[2], [3]]⟩

/-- The engine grants the certified subject access to a certified resource. -/
theorem demo_grants :
    Engine.grants demoParams (demoParams.pk 2)
      ⟨demoCert, demoParams.sign 2 5 demoCert.bytes⟩ demoCert.subject [2] = true :=
  engine_grants_issued demoParams 2 5 demoCert (by simp [demoCert])

end Demo
end Cert
end PCA

import RequestProject.Bytes

/-!
# A formal model of Ed25519 signature verification

This file develops the signature-verification model used by the certificate
(`PCA.Cert`) layer of the isolation engine.

The model is the standard Ed25519 / Schnorr structure, stated over an abstract
prime-order group `G` (a vector space over the scalar field `ZMod L`, `L` the
prime group order) equipped with

* a base point `B` of exact order `L`,
* a canonical 32-byte point encoding `encPt` / `decPt`,
* a hash function `H` mapping `(encoded nonce, encoded public key, message)`
  to a scalar challenge.

Signatures are 64 bytes: a 32-byte encoded nonce point `R` followed by a
32-byte little-endian *canonical* scalar `S` (values `≥ L` are rejected, which
is the malleability check of RFC 8032).

The results proved here are:

* `PCA.Cert.ed25519_verify_complete` — completeness: honestly produced
  signatures are accepted.
* `PCA.Cert.ed25519_verify_sound` — soundness: an accepted signature is
  necessarily a canonically encoded, well-formed Schnorr transcript satisfying
  the group verification equation, and it *determines the secret key*: for any
  discrete logarithm `r` of the nonce point and nonzero challenge, the public
  key equals `((S - r) / c) • B`.
* `PCA.Cert.ed25519_special_soundness` — two accepting signatures sharing a
  nonce but with different challenges extract the secret key.
* `PCA.Cert.ed25519_response_unique` — strong unforgeability at the byte
  level: an accepted signature is uniquely determined by its nonce component.
* `PCA.Cert.Params.ofZMod` — a concrete instantiation, showing the axioms of
  the model are consistent (non-vacuity).
-/

namespace PCA
namespace Cert

section Scalars

variable (L : ℕ)

/-- Canonical 32-byte little-endian encoding of a scalar. -/
def encScalar (s : ZMod L) : List UInt8 := natToLe s.val 32

/-- Canonical scalar decoding: 32 little-endian bytes whose value is `< L`.
Non-canonical encodings (value `≥ L`) are rejected. -/
def decScalar (bs : List UInt8) : Option (ZMod L) :=
  if bs.length = 32 ∧ leToNat bs < L then some ((leToNat bs : ZMod L)) else none

@[simp] theorem length_encScalar (s : ZMod L) : (encScalar L s).length = 32 := by
  simp [encScalar]

variable {L}

theorem decScalar_encScalar [NeZero L] (hL : L ≤ 2 ^ 256) (s : ZMod L) :
    decScalar L (encScalar L s) = some s := by
  have hval : s.val < L := ZMod.val_lt s
  have h256 : (256 : ℕ) ^ 32 = 2 ^ 256 := by norm_num
  have hlt : s.val < 256 ^ 32 := by omega
  have hval' : leToNat (encScalar L s) = s.val := by
    rw [encScalar]; exact leToNat_natToLe_of_lt hlt
  have hlen : (encScalar L s).length = 32 := length_encScalar L s
  unfold decScalar
  rw [if_pos ⟨hlen, by rw [hval']; exact hval⟩, hval', ZMod.natCast_zmod_val]

/-- Decoding is canonical: a byte string that decodes to `s` *is* the encoding of `s`. -/
theorem encScalar_decScalar [NeZero L] {bs : List UInt8} {s : ZMod L}
    (h : decScalar L bs = some s) : encScalar L s = bs := by
  unfold decScalar at h
  split at h
  · rename_i hc
    obtain ⟨hlen, hlt⟩ := hc
    have hs : s = ((leToNat bs : ℕ) : ZMod L) := by simpa using h.symm
    have hvs : s.val = leToNat bs := by
      rw [hs, ZMod.val_natCast_of_lt hlt]
    rw [encScalar, hvs, ← hlen, natToLe_leToNat]
  · exact absurd h (by simp)

end Scalars

/-- Static parameters of the Ed25519-style scheme: a prime-order group with a
base point, a canonical point encoding and a hash function. -/
structure Params (G : Type*) (L : ℕ) [AddCommGroup G] [Module (ZMod L) G] where
  /-- The base point. -/
  B : G
  /-- `B` has exact order `L`: no nonzero scalar kills it. -/
  hB : ∀ s : ZMod L, s • B = 0 → s = 0
  /-- Scalars fit in 32 bytes. -/
  hL : L ≤ 2 ^ 256
  /-- Point encoding. -/
  encPt : G → List UInt8
  /-- Encoded points are 32 bytes long. -/
  encPt_length : ∀ P, (encPt P).length = 32
  /-- Point decoding. -/
  decPt : List UInt8 → Option G
  /-- Decoding an encoded point recovers it. -/
  decPt_encPt : ∀ P, decPt (encPt P) = some P
  /-- The encoding is canonical: at most one byte string decodes to a given point. -/
  encPt_decPt : ∀ bs P, decPt bs = some P → encPt P = bs
  /-- The hash function, applied to (encoded nonce, encoded public key, message). -/
  H : List UInt8 → List UInt8 → List UInt8 → ZMod L

namespace Params

variable {G : Type*} {L : ℕ} [AddCommGroup G] [Module (ZMod L) G] [DecidableEq G]
variable (p : Params G L)

/-- The public key associated with the secret scalar `a`. -/
def pk (a : ZMod L) : List UInt8 := p.encPt (a • p.B)

/-- Ed25519 verification of a 64-byte signature `sigb` on `msg` under the
encoded public key `pkb`. -/
def verify (pkb msg sigb : List UInt8) : Bool :=
  (sigb.length == 64) &&
    (match p.decPt pkb, p.decPt (sigb.take 32), decScalar L (sigb.drop 32) with
     | some A, some R, some S =>
        decide (S • p.B = R + p.H (sigb.take 32) pkb msg • A)
     | _, _, _ => false)

/-- Deterministic Ed25519 signing with secret scalar `a` and nonce scalar `r`. -/
def sign (a r : ZMod L) (msg : List UInt8) : List UInt8 :=
  p.encPt (r • p.B) ++ encScalar L (r + p.H (p.encPt (r • p.B)) (p.pk a) msg * a)

theorem verify_iff (pkb msg sigb : List UInt8) :
    p.verify pkb msg sigb = true ↔
      sigb.length = 64 ∧
        ∃ A R : G, ∃ S : ZMod L,
          p.decPt pkb = some A ∧ p.decPt (sigb.take 32) = some R ∧
            decScalar L (sigb.drop 32) = some S ∧
            S • p.B = R + p.H (sigb.take 32) pkb msg • A := by
  unfold verify
  cases hA : p.decPt pkb with
  | none => simp
  | some A =>
    cases hR : p.decPt (sigb.take 32) with
    | none => simp
    | some R =>
      cases hS : decScalar L (sigb.drop 32) with
      | none => simp
      | some S =>
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
        constructor
        · rintro ⟨hlen, heq⟩
          exact ⟨hlen, A, R, S, rfl, rfl, rfl, heq⟩
        · rintro ⟨hlen, A', R', S', hA', hR', hS', heq⟩
          obtain rfl := Option.some.inj hA'
          obtain rfl := Option.some.inj hR'
          obtain rfl := Option.some.inj hS'
          exact ⟨hlen, heq⟩

end Params

section Theorems

variable {G : Type*} {L : ℕ} [AddCommGroup G] [Module (ZMod L) G] [DecidableEq G] [NeZero L]
variable (p : Params G L)

/-- **Completeness.** A signature produced by `sign` with secret scalar `a` is
accepted under the public key of `a`. -/
theorem ed25519_verify_complete (a r : ZMod L) (msg : List UInt8) :
    p.verify (p.pk a) msg (p.sign a r msg) = true := by
  have hlenR : (p.encPt (r • p.B)).length = 32 := p.encPt_length _
  have htake : (p.sign a r msg).take 32 = p.encPt (r • p.B) := by
    rw [Params.sign, List.take_left' hlenR]
  have hdrop : (p.sign a r msg).drop 32 =
      encScalar L (r + p.H (p.encPt (r • p.B)) (p.pk a) msg * a) := by
    rw [Params.sign, List.drop_left' hlenR]
  have hlen : (p.sign a r msg).length = 64 := by
    rw [Params.sign, List.length_append, hlenR, length_encScalar]
  rw [Params.verify_iff]
  refine ⟨hlen, a • p.B, r • p.B, r + p.H (p.encPt (r • p.B)) (p.pk a) msg * a, ?_, ?_, ?_, ?_⟩
  · rw [Params.pk]; exact p.decPt_encPt _
  · rw [htake]; exact p.decPt_encPt _
  · rw [hdrop]; exact decScalar_encScalar p.hL _
  · rw [htake, add_smul, mul_smul]

/-- **Soundness of Ed25519 verification.**

If the verifier accepts the 64-byte signature `sigb` on `msg` under the encoded
public key `pkb`, then:

* `pkb` and the nonce half of `sigb` are canonical point encodings of points
  `A` and `R`, and `sigb` is exactly `encPt R ++ encScalar S` — i.e. the
  accepted signature is in canonical (non-malleable) form;
* the Schnorr verification equation `S • B = R + c • A` holds, with
  `c = H (encPt R) (encPt A) msg`;
* the signature *determines the secret key*: whenever `r` is a discrete
  logarithm of the nonce point `R` and the challenge `c` is nonzero, the public
  key satisfies `A = ((S - r) / c) • B`, so `(S - r) / c` is the secret scalar.
-/
theorem ed25519_verify_sound [Fact (Nat.Prime L)] {pkb msg sigb : List UInt8}
    (h : p.verify pkb msg sigb = true) :
    ∃ (A R : G) (S : ZMod L),
      p.decPt pkb = some A ∧ p.encPt A = pkb ∧
      p.decPt (sigb.take 32) = some R ∧
      sigb = p.encPt R ++ encScalar L S ∧
      S • p.B = R + p.H (p.encPt R) (p.encPt A) msg • A ∧
      (∀ r : ZMod L, R = r • p.B →
        p.H (p.encPt R) (p.encPt A) msg ≠ 0 →
        A = ((S - r) * (p.H (p.encPt R) (p.encPt A) msg)⁻¹) • p.B) := by
  rw [Params.verify_iff] at h
  obtain ⟨hlen, A, R, S, hA, hR, hS, heq⟩ := h
  have hpkb : p.encPt A = pkb := p.encPt_decPt _ _ hA
  have hRb : p.encPt R = sigb.take 32 := p.encPt_decPt _ _ hR
  have hSb : encScalar L S = sigb.drop 32 := encScalar_decScalar hS
  have hsplit : sigb = p.encPt R ++ encScalar L S := by
    rw [hRb, hSb, List.take_append_drop]
  refine ⟨A, R, S, hA, hpkb, hR, hsplit, ?_, ?_⟩
  · rw [hRb, hpkb]; exact heq
  · intro r hr hc
    set c : ZMod L := p.H (p.encPt R) (p.encPt A) msg with hcdef
    have heq' : S • p.B = R + c • A := by rw [hcdef, hRb, hpkb]; exact heq
    rw [hr] at heq'
    have h1 : (S - r) • p.B = c • A := by
      rw [sub_smul]
      rw [heq']
      abel
    have h2 : ((S - r) * c⁻¹) • p.B = (c⁻¹ * c) • A := by
      rw [mul_comm (S - r) c⁻¹, mul_smul, h1, mul_smul]
    rw [inv_mul_cancel₀ hc, one_smul] at h2
    exact h2.symm

omit [DecidableEq G] [NeZero L] in
/-- **Special soundness.** Two accepted signatures that share the same nonce
point but have different challenges yield the secret key: the public key `A`
equals `x • B` for the extracted scalar `x = (S₁ - S₂) / (c₁ - c₂)`. -/
theorem ed25519_special_soundness [Fact (Nat.Prime L)] {A R : G} {S₁ S₂ c₁ c₂ : ZMod L}
    (h₁ : S₁ • p.B = R + c₁ • A) (h₂ : S₂ • p.B = R + c₂ • A) (hne : c₁ ≠ c₂) :
    A = ((S₁ - S₂) * (c₁ - c₂)⁻¹) • p.B := by
  have hc : c₁ - c₂ ≠ 0 := sub_ne_zero_of_ne hne
  have h1 : (S₁ - S₂) • p.B = (c₁ - c₂) • A := by
    rw [sub_smul, h₁, h₂, sub_smul]
    abel
  have h2 : ((S₁ - S₂) * (c₁ - c₂)⁻¹) • p.B = ((c₁ - c₂)⁻¹ * (c₁ - c₂)) • A := by
    rw [mul_comm (S₁ - S₂) (c₁ - c₂)⁻¹, mul_smul, h1, mul_smul]
  rw [inv_mul_cancel₀ hc, one_smul] at h2
  exact h2.symm

/-- **Strong unforgeability at the byte level (non-malleability).** Two accepted
signatures on the same message under the same key that share the same nonce
component are equal as byte strings. In particular the scalar `S` cannot be
mauled (e.g. by adding `L`) without breaking verification. -/
theorem ed25519_response_unique {pkb msg sigb sigb' : List UInt8}
    (h : p.verify pkb msg sigb = true) (h' : p.verify pkb msg sigb' = true)
    (hR : sigb.take 32 = sigb'.take 32) : sigb = sigb' := by
  rw [Params.verify_iff] at h h'
  obtain ⟨hlen, A, R, S, hA, hRd, hS, heq⟩ := h
  obtain ⟨hlen', A', R', S', hA', hRd', hS', heq'⟩ := h'
  rw [hA] at hA'
  rw [← hR, hRd] at hRd'
  rw [← hR] at heq'
  cases hA'; cases hRd'
  have hSS : S = S' := by
    have hz : (S - S') • p.B = 0 := by
      rw [sub_smul, heq, heq']
      abel
    exact sub_eq_zero.mp (p.hB _ hz)
  have hSb : encScalar L S = sigb.drop 32 := encScalar_decScalar hS
  have hSb' : encScalar L S' = sigb'.drop 32 := encScalar_decScalar hS'
  have hdrop : sigb.drop 32 = sigb'.drop 32 := by rw [← hSb, ← hSb', hSS]
  calc sigb = sigb.take 32 ++ sigb.drop 32 := (List.take_append_drop _ _).symm
    _ = sigb'.take 32 ++ sigb'.drop 32 := by rw [hR, hdrop]
    _ = sigb' := List.take_append_drop _ _

omit [NeZero L] in
/-- **Non-canonical scalars are rejected.** If the scalar half of the signature
encodes a value `≥ L` (the classical Ed25519 malleability trick of adding the
group order), verification fails. -/
theorem ed25519_reject_noncanonical {pkb msg sigb : List UInt8}
    (h : L ≤ leToNat (sigb.drop 32)) : p.verify pkb msg sigb = false := by
  cases hv : p.verify pkb msg sigb with
  | false => rfl
  | true =>
      rw [Params.verify_iff] at hv
      obtain ⟨-, A, R, S, -, -, hS, -⟩ := hv
      unfold decScalar at hS
      rw [if_neg (fun hc => absurd hc.2 (by omega))] at hS
      exact absurd hS (by simp)

end Theorems

section Instantiation

/-- A concrete instantiation of the model: the group is the scalar field itself
with base point `1` and canonical little-endian encodings. This witnesses that
the assumptions bundled in `Params` are consistent (the model is not vacuous). -/
def Params.ofZMod (L : ℕ) [NeZero L] (hL : L ≤ 2 ^ 256)
    (H : List UInt8 → List UInt8 → List UInt8 → ZMod L) : Params (ZMod L) L where
  B := 1
  hB := by intro s hs; simpa using hs
  hL := hL
  encPt := fun P => encScalar L P
  encPt_length := by intro P; simp
  decPt := fun bs => decScalar L bs
  decPt_encPt := by intro P; exact decScalar_encScalar hL P
  encPt_decPt := by intro bs P h; exact encScalar_decScalar h
  H := H

end Instantiation

end Cert
end PCA

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

import RequestProject.Ed25519

/-!
# The isolation engine's certificate model

An *isolation engine* mediates access of subjects to resources: a subject may
touch a resource only if it presents a capability certificate, signed by the
root authority, that names the subject and lists the resource.

This file gives:

* a concrete, prefix-free, **injective** serialization of certificates
  (`PCA.Cert.CapCert.bytes`, `PCA.Cert.cert_bytes_injective`);
* the engine's access-control decision procedure
  (`PCA.Cert.Engine.accepts`, `PCA.Cert.Engine.grants`);
* **completeness** of the engine (`PCA.Cert.engine_grants_issued`): a
  certificate honestly issued by the root authority is accepted, and access to
  each capability it lists is granted;
* **soundness / isolation** of the engine
  (`PCA.Cert.engine_sound`, `PCA.Cert.engine_isolation`): relative to an
  explicitly stated unforgeability assumption on the signature scheme, every
  access the engine grants is justified by a certificate that the authority
  actually issued; consequently a subject can never reach a resource that no
  issued certificate authorizes.

The unforgeability assumption is a hypothesis of the theorems (never an
axiom): it is the standard EUF-CMA statement, that any byte string carrying a
valid signature under the root key is one of the messages the authority signed.
-/

namespace PCA
namespace Cert

/-! ## Prefix-free serialization -/

/-- A length-prefixed byte string (4-byte little-endian length prefix). -/
def encBytes (bs : List UInt8) : List UInt8 := natToLe bs.length 4 ++ bs

/-- Concatenation of length-prefixed byte strings. -/
def encList : List (List UInt8) → List UInt8
  | [] => []
  | b :: rest => encBytes b ++ encList rest

/-- A byte string is serializable when its length fits in the 4-byte prefix. -/
def ShortBytes (bs : List UInt8) : Prop := bs.length < 2 ^ 32

theorem encBytes_inj_append {a b x y : List UInt8} (ha : ShortBytes a) (hb : ShortBytes b)
    (h : encBytes a ++ x = encBytes b ++ y) : a = b ∧ x = y := by
  have h4a : (natToLe a.length 4).length = 4 := length_natToLe _ _
  have h4b : (natToLe b.length 4).length = 4 := length_natToLe _ _
  have h' : natToLe a.length 4 ++ (a ++ x) = natToLe b.length 4 ++ (b ++ y) := by
    simpa [encBytes, List.append_assoc] using h
  obtain ⟨hpre, hrest⟩ := List.append_inj h' (by rw [h4a, h4b])
  have hlen : a.length = b.length := by
    have := congrArg leToNat hpre
    rw [leToNat_natToLe_of_lt (by simpa [ShortBytes] using ha),
      leToNat_natToLe_of_lt (by simpa [ShortBytes] using hb)] at this
    exact this
  exact List.append_inj hrest hlen

theorem encList_inj_append :
    ∀ {as bs : List (List UInt8)} {x y : List UInt8},
      (∀ a ∈ as, ShortBytes a) → (∀ b ∈ bs, ShortBytes b) → as.length = bs.length →
      encList as ++ x = encList bs ++ y → as = bs ∧ x = y
  | [], [], x, y, _, _, _, h => ⟨rfl, by simpa [encList] using h⟩
  | [], _ :: _, _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, hlen, _ => by simp at hlen
  | a :: as, b :: bs, x, y, ha, hb, hlen, h => by
      have h' : encBytes a ++ (encList as ++ x) = encBytes b ++ (encList bs ++ y) := by
        simpa [encList, List.append_assoc] using h
      obtain ⟨hab, hrest⟩ :=
        encBytes_inj_append (ha a (by simp)) (hb b (by simp)) h'
      obtain ⟨hasbs, hxy⟩ :=
        encList_inj_append (fun c hc => ha c (by simp [hc]))
          (fun c hc => hb c (by simp [hc])) (by simpa using hlen) hrest
      exact ⟨by rw [hab, hasbs], hxy⟩

/-! ## Certificates -/

/-- A capability certificate: it names a subject and the resources that subject
may access. -/
structure CapCert where
  /-- The subject the certificate is issued to. -/
  subject : List UInt8
  /-- The resources the subject may access. -/
  caps : List (List UInt8)
  deriving DecidableEq

/-- Serialization of a certificate: length-prefixed subject, then the number of
capabilities, then the length-prefixed capabilities. -/
def CapCert.bytes (c : CapCert) : List UInt8 :=
  encBytes c.subject ++ natToLe c.caps.length 4 ++ encList c.caps

/-- Well-formedness: every component fits in its length prefix. -/
def CapCert.WF (c : CapCert) : Prop :=
  ShortBytes c.subject ∧ c.caps.length < 2 ^ 32 ∧ ∀ r ∈ c.caps, ShortBytes r

/-- **The certificate serialization is injective** on well-formed certificates:
distinct certificates never share a signed representation. -/
theorem cert_bytes_injective {c c' : CapCert} (hc : c.WF) (hc' : c'.WF)
    (h : c.bytes = c'.bytes) : c = c' := by
  obtain ⟨hs, hn, hr⟩ := hc
  obtain ⟨hs', hn', hr'⟩ := hc'
  have h' : encBytes c.subject ++ (natToLe c.caps.length 4 ++ encList c.caps) =
      encBytes c'.subject ++ (natToLe c'.caps.length 4 ++ encList c'.caps) := by
    simpa [CapCert.bytes, List.append_assoc] using h
  obtain ⟨hsub, hrest⟩ := encBytes_inj_append hs hs' h'
  obtain ⟨hpre, htail⟩ :=
    List.append_inj hrest (by rw [length_natToLe, length_natToLe])
  have hlen : c.caps.length = c'.caps.length := by
    have := congrArg leToNat hpre
    rwa [leToNat_natToLe_of_lt hn, leToNat_natToLe_of_lt hn'] at this
  obtain ⟨hcaps, -⟩ := encList_inj_append (x := []) (y := []) hr hr' hlen (by simpa using htail)
  cases c; cases c'
  simp_all

/-! ## The engine -/

namespace Engine

variable {G : Type*} {L : ℕ} [AddCommGroup G] [Module (ZMod L) G] [DecidableEq G]

/-- A certificate together with the authority's signature on it. -/
structure SignedCert where
  /-- The certificate. -/
  cert : CapCert
  /-- The 64-byte Ed25519 signature over `cert.bytes`. -/
  sig : List UInt8

/-- The engine accepts a signed certificate when the signature verifies under
the root public key. -/
def accepts (p : Params G L) (rootPk : List UInt8) (sc : SignedCert) : Bool :=
  p.verify rootPk sc.cert.bytes sc.sig

/-- The engine grants `subj` access to `res` on presentation of `sc` when the
certificate is accepted, is issued to `subj`, and lists `res`. -/
def grants (p : Params G L) (rootPk : List UInt8) (sc : SignedCert)
    (subj res : List UInt8) : Bool :=
  accepts p rootPk sc && (sc.cert.subject == subj) && decide (res ∈ sc.cert.caps)

end Engine

section EngineTheorems

open Engine

variable {G : Type*} {L : ℕ} [AddCommGroup G] [Module (ZMod L) G] [DecidableEq G] [NeZero L]
variable (p : Params G L)

/-- **Engine completeness.** A certificate signed by the root authority (secret
scalar `a`, nonce `r`) is accepted, and the engine grants its subject access to
every resource the certificate lists. -/
theorem engine_grants_issued (a r : ZMod L) (c : CapCert) {res : List UInt8}
    (hres : res ∈ c.caps) :
    grants p (p.pk a) ⟨c, p.sign a r c.bytes⟩ c.subject res = true := by
  unfold grants accepts
  simp [ed25519_verify_complete p a r c.bytes, hres]

omit [NeZero L] in
/-- **Engine soundness.** Assume the signature scheme is unforgeable with
respect to the set `issued` of certificates the authority has signed, i.e. every
byte string carrying a valid signature under the root key is the serialization
of an issued certificate. Then any access the engine grants is authorized by an
issued certificate: it names the subject and lists the resource. -/
theorem engine_sound {rootPk : List UInt8} {issued : Set CapCert}
    (hWF : ∀ c ∈ issued, c.WF)
    (hEUF : ∀ msg sig, p.verify rootPk msg sig = true → ∃ c ∈ issued, c.bytes = msg)
    {sc : SignedCert} {subj res : List UInt8}
    (hsc : sc.cert.WF)
    (hgrant : grants p rootPk sc subj res = true) :
    ∃ c ∈ issued, c.subject = subj ∧ res ∈ c.caps := by
  unfold grants accepts at hgrant
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hgrant
  obtain ⟨⟨hver, hsubj⟩, hres⟩ := hgrant
  obtain ⟨c, hcmem, hcb⟩ := hEUF _ _ hver
  have hceq : c = sc.cert := cert_bytes_injective (hWF c hcmem) hsc hcb
  rw [hceq] at hcmem
  exact ⟨sc.cert, hcmem, hsubj, hres⟩

omit [NeZero L] in
/-- **Isolation.** Under the same unforgeability assumption, if no issued
certificate authorizes `subj` to use `res`, then the engine denies every
presented certificate: the subject is confined. -/
theorem engine_isolation {rootPk : List UInt8} {issued : Set CapCert}
    (hWF : ∀ c ∈ issued, c.WF)
    (hEUF : ∀ msg sig, p.verify rootPk msg sig = true → ∃ c ∈ issued, c.bytes = msg)
    {subj res : List UInt8}
    (hnone : ∀ c ∈ issued, c.subject = subj → res ∉ c.caps)
    (sc : SignedCert) (hsc : sc.cert.WF) :
    grants p rootPk sc subj res = false := by
  cases hg : grants p rootPk sc subj res with
  | false => rfl
  | true =>
      obtain ⟨c, hcmem, hsubj, hres⟩ := engine_sound p hWF hEUF hsc hg
      exact (hnone c hcmem hsubj hres).elim

omit [NeZero L] in
/-- **Confinement.** If every issued certificate for `subj` lists only resources
inside the policy set `allowed`, then every access the engine grants to `subj`
stays inside `allowed`. -/
theorem engine_confinement {rootPk : List UInt8} {issued : Set CapCert}
    {allowed : Set (List UInt8)}
    (hWF : ∀ c ∈ issued, c.WF)
    (hEUF : ∀ msg sig, p.verify rootPk msg sig = true → ∃ c ∈ issued, c.bytes = msg)
    {subj : List UInt8}
    (hpolicy : ∀ c ∈ issued, c.subject = subj → ∀ r ∈ c.caps, r ∈ allowed)
    {sc : SignedCert} {res : List UInt8} (hsc : sc.cert.WF)
    (hgrant : grants p rootPk sc subj res = true) :
    res ∈ allowed := by
  obtain ⟨c, hcmem, hsubj, hres⟩ := engine_sound p hWF hEUF hsc hgrant
  exact hpolicy c hcmem hsubj res hres

end EngineTheorems

end Cert
end PCA

