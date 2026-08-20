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
