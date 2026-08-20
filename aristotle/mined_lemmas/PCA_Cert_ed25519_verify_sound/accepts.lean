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

def accepts (p : Params G L) (rootPk : List UInt8) (sc : SignedCert) : Bool :=
  p.verify rootPk sc.cert.bytes sc.sig

/-- The engine grants `subj` access to `res` on presentation of `sc` when the
certificate is accepted, is issued to `subj`, and lists `res`. -/
