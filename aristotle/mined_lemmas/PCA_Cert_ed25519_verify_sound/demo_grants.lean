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
