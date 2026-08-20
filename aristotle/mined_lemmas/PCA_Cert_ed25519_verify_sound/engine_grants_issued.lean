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
